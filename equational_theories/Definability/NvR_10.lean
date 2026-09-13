import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2163`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation2163 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2163 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2163.models_iff G M).mp hM
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
      have b0e40 : (M.op x y) = (k x y) := by grind
      have b0e41 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e41
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e41
        | exact resolve b0e41 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e44 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e40
           grind)
        | exact superpose b0e40 b0e43
        | exact resolve b0e43 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e43
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
        have b1e38 : (M.op x y) = (k x y) := by grind
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
             have i₂ := b1e38
             grind)
          | exact superpose b1e38 b1e82
          | exact resolve b1e82 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e82
        have b1e84 : False := by grind
        exact b1e84
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e70 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e428 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e51 b2e71
          | (have j1 := b2e51 X1 X0
             grind)
          | exact resolve b2e71 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e71
        have b2e457 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e428 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e428
        have b2e3602 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e457 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e457
        have b2e3603 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e3602 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3602
        have b2e3631 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e3603 (σ X0)
             grind)
          | exact superpose b2e3603 b2e18
          | exact resolve b2e18 b2e3603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3638 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3631 X0
             have i₂ := b2e3603 X0
             grind)
          | exact superpose b2e3603 b2e3631
          | exact resolve b2e3631 b2e3603
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3603 b2e3631
        have b2e3993 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3638 x
             grind)
          | exact superpose b2e3638 b2e21
          | exact resolve b2e21 b2e3638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3638
        have b2e4054 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3993
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3993
          | exact resolve b2e3993 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3993
        have b2e4055 : False := by grind
        exact b2e4055
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
        have b3e39 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e39
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e39
          | exact resolve b3e39 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
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
        have b3e115 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b3e120 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e115
             have i₂ := b3e79
             grind)
          | exact superpose b3e79 b3e115
          | exact resolve b3e115 b3e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79 b3e115
        have b3e121 : False := by grind
        exact b3e121
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
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e78 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e79 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e371 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e58 b5e79
            | (have j1 := b5e58 X1 X0
               grind)
            | exact resolve b5e79 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e79
          have b5e396 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e371 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e371
          have b5e3467 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e396 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e396
          have b5e3468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e3467 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3467
          have b5e3496 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e3468 (σ X0)
               grind)
            | exact superpose b5e3468 b5e19
            | exact resolve b5e19 b5e3468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3503 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e3496 X0
               have i₂ := b5e3468 X0
               grind)
            | exact superpose b5e3468 b5e3496
            | exact resolve b5e3496 b5e3468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3468 b5e3496
          have b5e3882 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3503 y
               grind)
            | exact superpose b5e3503 b5e24
            | exact resolve b5e24 b5e3503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3503
          have b5e3940 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e3882
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3882
            | exact resolve b5e3882 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3882
          have b5e3941 : False := by grind
          exact b5e3941
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e27 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X2))) = X3 := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op (M.op x X2) X0) (M.op X0 X2)
             have i₂ := b6e12 X0 x X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b6e71 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e71 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e104 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28 (σ x) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e28
          | exact resolve b6e28 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e114 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 X0 (M.op X1 x) (M.op X1 X0)
             have i₂ := b6e28 X1 x X0
             grind)
          | exact superpose b6e28 b6e28
          | exact resolve b6e28 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e391 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (k x y))) := by
          first
          | (have i₁ := b6e104 (σ x)
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e104
          | exact resolve b6e104 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e412 : (σ x) = (M.op (σ y) (σ (k x y))) := by
          first
          | (have i₁ := b6e391
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e391
          | exact resolve b6e391 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e391
        have b6e501 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e412
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e412
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e412 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e412
        have b6e511 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e501
             have r₂ := b6e20
             grind)
          | exact resolve b6e501 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e501
        have b6e513 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b6e511
             have r₂ := b6e21
             grind)
          | exact resolve b6e511 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e511
        have b6e651 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b6e114 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e114
          | exact resolve b6e114 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e689 : (σ y) = (M.op (σ (k x y)) (σ x)) := by
          first
          | (have i₁ := b6e651
             have i₂ := b6e38
             grind)
          | exact superpose b6e38 b6e651
          | exact resolve b6e651 b6e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38 b6e651
        have b6e770 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e689
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e689
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e689 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e689
        have b6e788 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e770
             have r₂ := b6e20
             grind)
          | exact resolve b6e770 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e770
        have b6e789 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have r₁ := b6e788
             have r₂ := b6e21
             grind)
          | exact resolve b6e788 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e788
        have b6e901 : (σ (M.op y x)) = (M.op (M.op (σ y) (σ (M.op y x))) (σ y)) := by
          first
          | (have i₁ := b6e27 (σ (M.op y x))
             have i₂ := b6e789
             grind)
          | exact superpose b6e789 b6e27
          | exact resolve b6e27 b6e789
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e789
        have b6e913 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e901
             have i₂ := b6e513
             grind)
          | exact superpose b6e513 b6e901
          | exact resolve b6e901 b6e513
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e513 b6e901
        have b6e1423 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e1655 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1423
        have b6e3491 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1655
             grind)
          | exact superpose b6e1655 b6e13
          | exact resolve b6e13 b6e1655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1655
        have b6e3505 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3491
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e3491
          | exact resolve b6e3491 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3491
        have b6e3704 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e83 x x
             have i₂ := b6e3505
             grind)
          | exact superpose b6e3505 b6e83
          | (have j0 := b6e83 x y
             grind)
          | exact resolve b6e83 b6e3505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e3705 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3704
        have b6e3715 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3705
             have r₂ := b6e20
             grind)
          | exact resolve b6e3705 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3705
        have b6e3809 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e81 x
             have i₂ := b6e3715
             grind)
          | exact superpose b6e3715 b6e81
          | exact resolve b6e81 b6e3715
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e3715
        have b6e4070 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3505
             have i₂ := b6e3809
             grind)
          | exact superpose b6e3809 b6e3505
          | exact resolve b6e3505 b6e3809
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3505 b6e3809
        have b6e4073 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e4070
        have b6e4075 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e4073
             have r₂ := b6e20
             grind)
          | exact resolve b6e4073 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4073
        have b6e4131 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e4075
             grind)
          | exact superpose b6e4075 b6e19
          | exact resolve b6e19 b6e4075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4147 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e913
             have i₂ := b6e4075
             grind)
          | exact superpose b6e4075 b6e913
          | exact resolve b6e913 b6e4075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e913
        have b6e4149 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e4075
             grind)
          | exact superpose b6e4075 b6e13
          | exact resolve b6e13 b6e4075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4166 : x = y := by
          first
          | (have i₁ := b6e4149
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4149
          | exact resolve b6e4149 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4149
        have b6e4168 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e4147
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4147
          | exact resolve b6e4147 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4147
        have b6e4177 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4131
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4131
          | exact resolve b6e4131 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4131
        have b6e4183 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4168
             have i₂ := b6e4166
             grind)
          | exact superpose b6e4166 b6e4168
          | exact resolve b6e4168 b6e4166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4168
        have b6e4189 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4177
             have i₂ := b6e4075
             grind)
          | exact superpose b6e4075 b6e4177
          | exact resolve b6e4177 b6e4075
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4075 b6e4177
        have b6e4198 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4189
             have i₂ := b6e4166
             grind)
          | exact superpose b6e4166 b6e4189
          | exact resolve b6e4189 b6e4166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4166 b6e4189
        have b6e4200 : False := by grind
        exact b6e4200
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
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
          have b7e34 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X2))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op (M.op x X2) X0) (M.op X0 X2)
               have i₂ := b7e13 X0 x X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b7e48 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
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
          have b7e83 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e95 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e129 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e140 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 (M.op X1 x) (M.op X1 X0)
               have i₂ := b7e34 X1 x X0
               grind)
            | exact superpose b7e34 b7e34
            | exact resolve b7e34 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e399 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ (k y x))) := by
            first
            | (have i₁ := b7e129 (σ y)
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e129
            | exact resolve b7e129 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e129
          have b7e418 : (σ y) = (M.op (σ x) (σ (k y x))) := by
            first
            | (have i₁ := b7e399
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e399
            | exact resolve b7e399 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e399
          have b7e509 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e418
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e418
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e418 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e418
          have b7e519 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e509
               have r₂ := b7e22
               grind)
            | exact resolve b7e509 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e509
          have b7e523 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have r₁ := b7e519
               have r₂ := b7e21
               grind)
            | exact resolve b7e519 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e519
          have b7e889 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e140 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e140
            | exact resolve b7e140 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e140
          have b7e925 : (σ x) = (M.op (σ (k y x)) (σ y)) := by
            first
            | (have i₁ := b7e889
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e889
            | exact resolve b7e889 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48 b7e889
          have b7e1081 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e925
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e925
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e925 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e925
          have b7e1110 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e1081
               have r₂ := b7e22
               grind)
            | exact resolve b7e1081 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1081
          have b7e1113 : (σ x) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have r₁ := b7e1110
               have r₂ := b7e21
               grind)
            | exact resolve b7e1110 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1110
          have b7e1254 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b7e33 (σ (M.op x y))
               have i₂ := b7e1113
               grind)
            | exact superpose b7e1113 b7e33
            | exact resolve b7e33 b7e1113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e1113
          have b7e1271 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e1254
               have i₂ := b7e523
               grind)
            | exact superpose b7e523 b7e1254
            | exact resolve b7e1254 b7e523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e523 b7e1254
          have b7e1486 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
          have b7e1714 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1486
          have b7e2518 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1714
               grind)
            | exact superpose b7e1714 b7e14
            | exact resolve b7e14 b7e1714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1714
          have b7e2532 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2518
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2518
            | exact resolve b7e2518 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2518
          have b7e2990 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e95 y y
               have i₂ := b7e2532
               grind)
            | exact superpose b7e2532 b7e95
            | (have j0 := b7e95 y x
               grind)
            | exact resolve b7e95 b7e2532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e2991 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2990
          have b7e3001 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2991
               have r₂ := b7e22
               grind)
            | exact resolve b7e2991 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2991
          have b7e3488 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e93 y
               have i₂ := b7e3001
               grind)
            | exact superpose b7e3001 b7e93
            | exact resolve b7e93 b7e3001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e3001
          have b7e3858 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e2532
               have i₂ := b7e3488
               grind)
            | exact superpose b7e3488 b7e2532
            | exact resolve b7e2532 b7e3488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2532 b7e3488
          have b7e3861 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3858
          have b7e3863 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3861
               have r₂ := b7e22
               grind)
            | exact resolve b7e3861 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3861
          have b7e3956 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e3863
               grind)
            | exact superpose b7e3863 b7e20
            | exact resolve b7e20 b7e3863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3973 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e1271
               have i₂ := b7e3863
               grind)
            | exact superpose b7e3863 b7e1271
            | exact resolve b7e1271 b7e3863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1271 b7e3863
          have b7e3996 : False := by grind
          exact b7e3996
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
          have b8e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
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
          have b8e320 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e321 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e320
               have r₂ := b8e23
               grind)
            | exact resolve b8e320 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e320
          have b8e322 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e321
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e321
            | exact resolve b8e321 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e321
          have b8e323 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e322
               grind)
            | exact superpose b8e322 b8e20
            | exact resolve b8e20 b8e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e409 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e323
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e323
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e323 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e323
          have b8e415 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e409
          have b8e418 : y = (M.op x x) := by
            first
            | (have r₁ := b8e415
               have r₂ := b8e22
               grind)
            | exact resolve b8e415 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e415
          have b8e419 : False := by grind
          exact b8e419

/-- `Equation2163`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation2163 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2163 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2163.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e242 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e81 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e81
        | exact resolve b0e81 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e243 : (M.op x y) = (k y x) := by
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
      have b0e246 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e242
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e242
        | exact resolve b0e242 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e242
      have b0e247 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e246
           have i₂ := b0e243
           grind)
        | exact superpose b0e243 b0e246
        | exact resolve b0e246 b0e243
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e243 b0e246
      have b0e248 : False := by grind
      exact b0e248
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e39 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
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
        have b1e115 : (σ (M.op x y)) ≠ (σ (k y x)) := by
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
        have b1e241 : (M.op x y) = (k y x) := by
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
        have b1e247 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e115
             have i₂ := b1e241
             grind)
          | exact superpose b1e241 b1e115
          | exact resolve b1e115 b1e241
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115 b1e241
        have b1e249 : False := by grind
        exact b1e249
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b2e51 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b2e421 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 X1
             grind)
          | (have i₁ := b2e71 X0
             have i₂ := b2e51 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e51 b2e71
          | (have j1 := b2e51 X1 X0
             grind)
          | exact resolve b2e71 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e71
        have b2e450 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e421 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e421
        have b2e3593 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e450 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e450
        have b2e3594 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e3593 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3593
        have b2e3614 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e3594 (σ X0)
             grind)
          | exact superpose b2e3594 b2e18
          | exact resolve b2e18 b2e3594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e3621 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e3614 X0
             have i₂ := b2e3594 X0
             grind)
          | exact superpose b2e3594 b2e3614
          | exact resolve b2e3614 b2e3594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3594 b2e3614
        have b2e3976 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e3621 x
             grind)
          | exact superpose b2e3621 b2e21
          | exact resolve b2e21 b2e3621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3621
        have b2e4037 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e3976
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e3976
          | exact resolve b2e3976 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3976
        have b2e4038 : False := by grind
        exact b2e4038
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e44 : (M.op x y) = (k y x) := by grind
          have b4e45 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e45
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e45
            | exact resolve b4e45 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e47
            | exact resolve b4e47 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e47
          have b4e49 : False := by grind
          exact b4e49
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b5e58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b5e364 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 X1
               grind)
            | (have i₁ := b5e79 X0
               have i₂ := b5e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e58 b5e79
            | (have j1 := b5e58 X1 X0
               grind)
            | exact resolve b5e79 b5e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58 b5e79
          have b5e389 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e364 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e364
          have b5e3454 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e389 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e389
          have b5e3455 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e3454 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3454
          have b5e3475 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e3455 (σ X0)
               grind)
            | exact superpose b5e3455 b5e19
            | exact resolve b5e19 b5e3455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3482 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e3475 X0
               have i₂ := b5e3455 X0
               grind)
            | exact superpose b5e3455 b5e3475
            | exact resolve b5e3475 b5e3455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3455 b5e3475
          have b5e3861 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e3482 y
               grind)
            | exact superpose b5e3482 b5e24
            | exact resolve b5e24 b5e3482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3482
          have b5e3918 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e3861
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e3861
            | exact resolve b5e3861 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3861
          have b5e3919 : False := by grind
          exact b5e3919
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e27 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X2))) = X3 := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e12 X3 (M.op (M.op x X2) X0) (M.op X0 X2)
             have i₂ := b6e12 X0 x X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b6e70 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
        have b6e82 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e70 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e131 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e28 (σ x) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e28
          | exact resolve b6e28 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e141 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e28 X0 (M.op X1 x) (M.op X1 X0)
             have i₂ := b6e28 X1 x X0
             grind)
          | exact superpose b6e28 b6e28
          | exact resolve b6e28 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e183 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e80 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e80
          | exact resolve b6e80 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e189 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b6e183
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e183
          | exact resolve b6e183 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e183
        have b6e528 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ (k y x))) := by
          first
          | (have i₁ := b6e131 (σ x)
             have i₂ := b6e189
             grind)
          | exact superpose b6e189 b6e131
          | exact resolve b6e131 b6e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e131
        have b6e549 : (σ x) = (M.op (σ y) (σ (k y x))) := by
          first
          | (have i₁ := b6e528
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e528
          | exact resolve b6e528 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e528
        have b6e650 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e549
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e549
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e549 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e549
        have b6e668 : (σ x) = (M.op (σ y) (σ (M.op y x))) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e650
             have r₂ := b6e21
             grind)
          | exact resolve b6e650 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e650
        have b6e671 : (σ x) = (M.op (σ y) (σ (M.op y x))) := by
          first
          | (have r₁ := b6e668
             have r₂ := b6e20
             grind)
          | exact resolve b6e668 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e668
        have b6e1034 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b6e141 (σ x) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e141
          | exact resolve b6e141 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e1085 : (σ y) = (M.op (σ (k y x)) (σ x)) := by
          first
          | (have i₁ := b6e1034
             have i₂ := b6e189
             grind)
          | exact superpose b6e189 b6e1034
          | exact resolve b6e1034 b6e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e189 b6e1034
        have b6e1228 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e1085
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e1085
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e1085 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1085
        have b6e1259 : (σ y) = (M.op (σ (M.op y x)) (σ x)) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e1228
             have r₂ := b6e21
             grind)
          | exact resolve b6e1228 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1228
        have b6e1262 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
          first
          | (have r₁ := b6e1259
             have r₂ := b6e20
             grind)
          | exact resolve b6e1259 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1259
        have b6e1441 : (σ (M.op y x)) = (M.op (M.op (σ y) (σ (M.op y x))) (σ y)) := by
          first
          | (have i₁ := b6e27 (σ (M.op y x))
             have i₂ := b6e1262
             grind)
          | exact superpose b6e1262 b6e27
          | exact resolve b6e27 b6e1262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27 b6e1262
        have b6e1460 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e1441
             have i₂ := b6e671
             grind)
          | exact superpose b6e671 b6e1441
          | exact resolve b6e1441 b6e671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e671 b6e1441
        have b6e1474 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e1704 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1474
        have b6e2951 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1704
             grind)
          | exact superpose b6e1704 b6e13
          | exact resolve b6e13 b6e1704
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1704
        have b6e2965 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2951
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2951
          | exact resolve b6e2951 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2951
        have b6e3449 : y = (M.op x x) ∨ x = (M.op x x) ∨ y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e82 x x
             have i₂ := b6e2965
             grind)
          | exact superpose b6e2965 b6e82
          | (have j0 := b6e82 x y
             grind)
          | exact resolve b6e82 b6e2965
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82
        have b6e3450 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3449
        have b6e3460 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3450
             have r₂ := b6e20
             grind)
          | exact resolve b6e3450 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3450
        have b6e3661 : (M.op x x) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e80 x
             have i₂ := b6e3460
             grind)
          | exact superpose b6e3460 b6e80
          | exact resolve b6e80 b6e3460
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e80 b6e3460
        have b6e3835 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2965
             have i₂ := b6e3661
             grind)
          | exact superpose b6e3661 b6e2965
          | exact resolve b6e2965 b6e3661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2965 b6e3661
        have b6e3838 : y = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3835
        have b6e3840 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3838
             have r₂ := b6e20
             grind)
          | exact resolve b6e3838 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3838
        have b6e4115 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e3840
             grind)
          | exact superpose b6e3840 b6e19
          | exact resolve b6e19 b6e3840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4130 : (M.op (σ x) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e1460
             have i₂ := b6e3840
             grind)
          | exact superpose b6e3840 b6e1460
          | exact resolve b6e1460 b6e3840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1460
        have b6e4131 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3840
             grind)
          | exact superpose b6e3840 b6e13
          | exact resolve b6e13 b6e3840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4148 : x = y := by
          first
          | (have i₁ := b6e4131
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e4131
          | exact resolve b6e4131 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4131
        have b6e4149 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e4130
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4130
          | exact resolve b6e4130 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4130
        have b6e4157 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e4115
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e4115
          | exact resolve b6e4115 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4115
        have b6e4162 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4149
             have i₂ := b6e4148
             grind)
          | exact superpose b6e4148 b6e4149
          | exact resolve b6e4149 b6e4148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4149
        have b6e4168 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b6e4157
             have i₂ := b6e3840
             grind)
          | exact superpose b6e3840 b6e4157
          | exact resolve b6e4157 b6e3840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3840 b6e4157
        have b6e4178 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e4168
             have i₂ := b6e4148
             grind)
          | exact superpose b6e4148 b6e4168
          | exact resolve b6e4168 b6e4148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4148 b6e4168
        have b6e4181 : False := by grind
        exact b6e4181
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X2)) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e33 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 (σ y))) = X0 := by
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
          have b7e34 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X3) (M.op X3 (M.op X0 X2))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op (M.op x X2) X0) (M.op X0 X2)
               have i₂ := b7e13 X0 x X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b7e67 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
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
          have b7e77 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          have b7e78 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
          have b7e90 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e91 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e23
               grind)
            | exact resolve b7e77 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e92 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e91
            | exact resolve b7e91 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e143 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op X0 (σ x))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e154 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 (M.op X1 x) (M.op X1 X0)
               have i₂ := b7e34 X1 x X0
               grind)
            | exact superpose b7e34 b7e34
            | exact resolve b7e34 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e365 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ (k x y))) := by
            first
            | (have i₁ := b7e143 (σ y)
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e143
            | exact resolve b7e143 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143
          have b7e388 : (σ y) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b7e365
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e365
            | exact resolve b7e365 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e365
          have b7e396 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e388
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e388
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e388 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e388
          have b7e406 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e396
               have r₂ := b7e21
               grind)
            | exact resolve b7e396 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e396
          have b7e408 : (σ y) = (M.op (σ x) (σ (M.op x y))) := by
            first
            | (have r₁ := b7e406
               have r₂ := b7e22
               grind)
            | exact resolve b7e406 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e406
          have b7e481 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e67 x y
               grind)
            | exact superpose b7e67 b7e49
            | (have j1 := b7e67 x y
               grind)
            | exact resolve b7e49 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49 b7e67
          have b7e523 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          clear b7e481
          have b7e535 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e523
               have r₂ := b7e21
               grind)
            | exact resolve b7e523 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e523
          have b7e792 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e154 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e154
            | exact resolve b7e154 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154
          have b7e829 : (σ x) = (M.op (σ (k x y)) (σ y)) := by
            first
            | (have i₁ := b7e792
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e792
            | exact resolve b7e792 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92 b7e792
          have b7e836 : (σ x) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b7e829
               have i₂ := b7e535
               grind)
            | exact superpose b7e535 b7e829
            | exact resolve b7e829 b7e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e535 b7e829
          have b7e956 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b7e33 (σ (M.op x y))
               have i₂ := b7e836
               grind)
            | exact superpose b7e836 b7e33
            | exact resolve b7e33 b7e836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e836
          have b7e969 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e956
               have i₂ := b7e408
               grind)
            | exact superpose b7e408 b7e956
            | exact resolve b7e956 b7e408
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e408 b7e956
          have b7e1586 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
          have b7e1820 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e1586
          have b7e1905 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e1820
               grind)
            | exact superpose b7e1820 b7e14
            | exact resolve b7e14 b7e1820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1820
          have b7e1919 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1905
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1905
            | exact resolve b7e1905 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1905
          have b7e2167 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e90 y y
               have i₂ := b7e1919
               grind)
            | exact superpose b7e1919 b7e90
            | (have j0 := b7e90 y x
               grind)
            | exact resolve b7e90 b7e1919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e2168 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e2167
          have b7e2178 : y = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e2168
               have r₂ := b7e22
               grind)
            | exact resolve b7e2168 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2168
          have b7e2443 : (M.op y y) = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e88 y
               have i₂ := b7e2178
               grind)
            | exact superpose b7e2178 b7e88
            | exact resolve b7e88 b7e2178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88 b7e2178
          have b7e3149 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e1919
               have i₂ := b7e2443
               grind)
            | exact superpose b7e2443 b7e1919
            | exact resolve b7e1919 b7e2443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1919 b7e2443
          have b7e3152 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b7e3149
          have b7e3154 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e3152
               have r₂ := b7e22
               grind)
            | exact resolve b7e3152 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3152
          have b7e3727 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e3154
               grind)
            | exact superpose b7e3154 b7e20
            | exact resolve b7e20 b7e3154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3743 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e969
               have i₂ := b7e3154
               grind)
            | exact superpose b7e3154 b7e969
            | exact resolve b7e969 b7e3154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e969 b7e3154
          have b7e3765 : False := by grind
          exact b7e3765
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
          have b8e308 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e309 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e308
               have r₂ := b8e24
               grind)
            | exact resolve b8e308 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308
          have b8e310 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e309
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e309
            | exact resolve b8e309 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309
          have b8e311 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e310
               grind)
            | exact superpose b8e310 b8e20
            | exact resolve b8e20 b8e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e310
          have b8e325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e311
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e311
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e311 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e326 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e325
          have b8e327 : x = (M.op y y) := by
            first
            | (have r₁ := b8e326
               have r₂ := b8e21
               grind)
            | exact resolve b8e326 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e326
          have b8e329 : False := by grind
          exact b8e329

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation2301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
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
      have b0e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e42 (σ X0)
           grind)
        | exact superpose b0e42 b0e17
        | exact resolve b0e17 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e48 X0
           have i₂ := b0e42 X0
           grind)
        | exact superpose b0e42 b0e48
        | exact resolve b0e48 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e48
      have b0e180 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e53 x
           grind)
        | exact superpose b0e53 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e53 x
           grind)
        | exact resolve b0e22 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e53
      have b0e189 : False := by grind
      exact b0e189
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
        have b1e50 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e51 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e51
        have b1e54 : (k x y) = (M.op y y) := by grind
        clear b1e50
        have b1e55 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e52 y
             grind)
          | exact superpose b1e52 b1e55
          | exact resolve b1e55 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e52 (σ X0)
             grind)
          | exact superpose b1e52 b1e18
          | exact resolve b1e18 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e58 X0
             have i₂ := b1e52 X0
             grind)
          | exact superpose b1e52 b1e58
          | exact resolve b1e58 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e58
        have b1e72 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e74 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e72
          | (have j0 := b1e72 X0
             grind)
          | exact resolve b1e72 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e124 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e23
          | exact resolve b1e23 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e603 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e74 (σ x)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e74
          | (have j0 := b1e74 (σ x)
             grind)
          | (have r₁ := b1e74 (σ x)
             have r₂ := b1e56
             grind)
          | exact resolve b1e74 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e74
        have b1e604 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e603
        have b1e605 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e604
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e604
          | exact resolve b1e604 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e604
        have b1e607 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e605
             have r₂ := b1e124
             grind)
          | exact resolve b1e605 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e605
        have b1e609 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e607
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e607
          | exact resolve b1e607 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e607
        have b1e610 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e609
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e609
          | exact resolve b1e609 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e609
        have b1e611 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e610
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e610
          | exact resolve b1e610 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e610
        have b1e612 : False := by grind
        exact b1e612
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
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : (k x y) = (M.op y y) := by grind
        clear b2e48
        have b2e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e49 (σ X0)
             grind)
          | exact superpose b2e49 b2e18
          | exact resolve b2e18 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e52 X0
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e52
          | exact resolve b2e52 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e52
        have b2e87 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e135 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e59 y
             grind)
          | exact superpose b2e59 b2e22
          | exact resolve b2e22 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e954 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e955 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e954
             have r₂ := b2e21
             grind)
          | exact resolve b2e954 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e954
        have b2e958 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e955
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e955
          | exact resolve b2e955 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e955
        have b2e960 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e958
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e958
          | exact resolve b2e958 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e958
        have b2e961 : False := by grind
        exact b2e961
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
        have b3e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e51
        have b3e55 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e53
          | exact resolve b3e53 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e52 (σ X0)
             grind)
          | exact superpose b3e52 b3e18
          | exact resolve b3e18 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e52 X0
             grind)
          | exact superpose b3e52 b3e58
          | exact resolve b3e58 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e72 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e15
          | exact resolve b3e15 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e78 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
        have b3e79 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e78
          | exact resolve b3e78 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e52 y
             grind)
          | exact superpose b3e52 b3e79
          | exact resolve b3e79 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e79
        have b3e81 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e80
          | exact resolve b3e80 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e183 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e65 x
             grind)
          | exact superpose b3e65 b3e23
          | exact resolve b3e23 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e65
        have b3e219 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e220 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e219
             have r₂ := b3e20
             grind)
          | exact resolve b3e219 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e219
        have b3e224 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e220
             grind)
          | exact superpose b3e220 b3e81
          | exact resolve b3e81 b3e220
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e220
        have b3e228 : False := by grind
        exact b3e228
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
          have b4e65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e65
          have b4e69 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e67
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e67
            | exact resolve b4e67 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e71 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e69
               have i₂ := b4e66 y
               grind)
            | exact superpose b4e66 b4e69
            | exact resolve b4e69 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e69
          have b4e72 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e71
            | exact resolve b4e71 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e73 : False := by grind
          exact b4e73
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
          have b5e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e63 (σ X0)
               grind)
            | exact superpose b5e63 b5e19
            | exact resolve b5e19 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e67 X0
               have i₂ := b5e63 X0
               grind)
            | exact superpose b5e63 b5e67
            | exact resolve b5e67 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e67
          have b5e85 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e120 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e247 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e248 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e247
               have r₂ := b5e21
               grind)
            | exact resolve b5e247 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e247
          have b5e1193 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1194 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1193
               have r₂ := b5e23
               grind)
            | exact resolve b5e1193 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1193
          have b5e1198 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1194
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1194
            | exact resolve b5e1194 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1194
          have b5e1202 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1198
               have i₂ := b5e248
               grind)
            | exact superpose b5e248 b5e1198
            | exact resolve b5e1198 b5e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248 b5e1198
          have b5e1208 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1202
               grind)
            | exact superpose b5e1202 b5e23
            | exact resolve b5e23 b5e1202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1202
          have b5e1218 : False := by grind
          exact b5e1218
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
        have b6e48 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e48
        have b6e51 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e50
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e50
          | exact resolve b6e50 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e15
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e72 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e70
        have b6e73 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e72
          | exact resolve b6e72 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e74 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e49 y
             grind)
          | exact superpose b6e49 b6e73
          | exact resolve b6e73 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e73
        have b6e125 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e74
             grind)
          | exact superpose b6e74 b6e13
          | exact resolve b6e13 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e126 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e125
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e125
          | exact resolve b6e125 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e143 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e126
             grind)
          | exact superpose b6e126 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e144 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e143
        have b6e146 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e144
             have r₂ := b6e21
             grind)
          | exact resolve b6e144 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e148 : False := by grind
        exact b6e148
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
          have b7e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e62
          have b7e65 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e63 y
               grind)
            | exact superpose b7e63 b7e65
            | exact resolve b7e65 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e63 (σ X0)
               grind)
            | exact superpose b7e63 b7e19
            | exact resolve b7e19 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e68 X0
               have i₂ := b7e63 X0
               grind)
            | exact superpose b7e63 b7e68
            | exact resolve b7e68 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e68
          have b7e86 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e86 X0
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e86
            | (have j0 := b7e86 X0
               grind)
            | exact resolve b7e86 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e23
            | exact resolve b7e23 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e89
            | exact resolve b7e89 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e108 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e108 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e108
          have b7e589 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e88 (σ x)
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e88
            | (have j0 := b7e88 (σ x)
               grind)
            | (have r₁ := b7e88 (σ x)
               have r₂ := b7e66
               grind)
            | exact resolve b7e88 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e88
          have b7e590 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e589
          have b7e591 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e590
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e590
            | exact resolve b7e590 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e590
          have b7e593 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e591
               have r₂ := b7e94
               grind)
            | exact resolve b7e591 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e591
          have b7e595 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e593
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e593
            | exact resolve b7e593 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e593
          have b7e596 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e595
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e595
            | exact resolve b7e595 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e595
          have b7e598 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e596
               have i₂ := b7e127 x y
               grind)
            | exact superpose b7e127 b7e596
            | (have j1 := b7e127 x y
               grind)
            | exact resolve b7e596 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e600 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e596
               grind)
            | exact superpose b7e596 b7e14
            | exact resolve b7e14 b7e596
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e596
          have b7e619 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e600
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e600
            | exact resolve b7e600 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e600
          have b7e621 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e598
               have r₂ := b7e94
               grind)
            | exact resolve b7e598 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e598
          have b7e624 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e621
               have r₂ := b7e22
               grind)
            | exact resolve b7e621 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e621
          have b7e625 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e624
               have i₂ := b7e619
               grind)
            | exact superpose b7e619 b7e624
            | exact resolve b7e624 b7e619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e619 b7e624
          have b7e626 : False := by grind
          exact b7e626
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
          have b8e113 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1000 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e999
               have r₂ := b8e23
               grind)
            | exact resolve b8e999 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e999
          have b8e1003 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1000
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1000
            | exact resolve b8e1000 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1000
          have b8e1010 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1003
               grind)
            | exact superpose b8e1003 b8e20
            | exact resolve b8e20 b8e1003
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1003
          have b8e1076 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1010
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1010
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1010 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1010
          have b8e1077 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1076
          have b8e1079 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1077
               have r₂ := b8e21
               grind)
            | exact resolve b8e1077 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1077
          have b8e1082 : False := by grind
          exact b8e1082

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation2301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y x) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e21 X0 X1
           grind)
        | exact superpose b0e21 b0e12
        | exact resolve b0e12 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e38 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear b0e40
      have b0e43 : (k x y) = (M.op y y) := by grind
      clear b0e38
      have b0e44 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
      have b0e45 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e43
           grind)
        | exact superpose b0e43 b0e44
        | exact resolve b0e44 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e44
      have b0e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e41 (σ X0)
           grind)
        | exact superpose b0e41 b0e17
        | exact resolve b0e17 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e41 (τ X0)
           grind)
        | exact superpose b0e41 b0e22
        | exact resolve b0e22 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e49
        | exact resolve b0e49 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e47 X0
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e47
        | exact resolve b0e47 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e54 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e50
        | exact resolve b0e50 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e50
      have b0e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e15 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e15 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
      have b0e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e77 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e77
        | (have j0 := b0e77 X0 X1
           grind)
        | exact resolve b0e77 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e90 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e84 X0 X1
           have j1 := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X0 X1
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X1 X0
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X1 X1
           have r₂ := b0e81 X1 X1
           grind)
        | exact resolve b0e84 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81 b0e84
      have b0e93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e88 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e88
        | (have j0 := b0e88 X0 X1
           grind)
        | exact resolve b0e88 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e108 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e28
        | exact resolve b0e28 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e179 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (σ X0)
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e15
        | (have j0 := b0e15 X1 (σ X0)
           grind)
        | exact resolve b0e15 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e180 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e14
        | (have j0 := b0e14 (σ X0) X1
           grind)
        | exact resolve b0e14 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e195 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e16 X1 (τ X0)
           grind)
        | (have i₁ := b0e54 X0
           have i₂ := b0e16 (τ X0) (τ X0)
           grind)
        | exact superpose b0e16 b0e54
        | (have j1 := b0e16 X1 (τ X0)
           grind)
        | exact resolve b0e54 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e202 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op (τ X0) (τ X0))
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e12
        | exact resolve b0e12 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e324 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (τ X0) X1
           have i₂ := b0e202 X0
           grind)
        | exact superpose b0e202 b0e14
        | (have j0 := b0e14 (τ X0) X1
           grind)
        | exact resolve b0e14 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e376 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 X1
           have i₂ := b0e90 X1 (τ X0)
           grind)
        | exact superpose b0e90 b0e21
        | (have j1 := b0e90 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e379 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e90 (τ X0) X1
           grind)
        | exact superpose b0e90 b0e22
        | (have j1 := b0e90 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e399 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e376 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e376
        | (have j0 := b0e376 X0 X1
           grind)
        | exact resolve b0e376 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e376
      have b0e419 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e399 X0 X1
           have i₂ := b0e202 X0
           grind)
        | exact superpose b0e202 b0e399
        | (have j0 := b0e399 X0 X1
           grind)
        | exact resolve b0e399 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e202 b0e399
      have b0e1448 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) (σ X1)
           have i₂ := b0e93 X1 X0
           grind)
        | exact superpose b0e93 b0e14
        | (have j0 := b0e14 (σ X0) (σ X1)
           have j1 := b0e93 X1 X0
           grind)
        | exact resolve b0e14 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1479 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1481 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1482 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e1529 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e1448 X0 X1
           have j1 := b0e180 X0 (σ X1)
           grind)
        | (have r₁ := b0e1448 X0 X0
           have r₂ := b0e180 X0 (σ X0)
           grind)
        | (have r₁ := b0e1448 X0 X1
           have r₂ := b0e180 X0 (σ X1)
           grind)
        | exact resolve b0e1448 b0e180
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e180 b0e1448
      have b0e1583 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1529 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e1529
        | (have j0 := b0e1529 X0 X1
           grind)
        | exact resolve b0e1529 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1529
      have b0e1619 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1583 X0 X1
           have i₂ := b0e52 X1
           grind)
        | exact superpose b0e52 b0e1583
        | (have j0 := b0e1583 X0 X1
           grind)
        | exact resolve b0e1583 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1583
      have b0e1641 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1619 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1619
        | (have j0 := b0e1619 X0 X1
           grind)
        | exact resolve b0e1619 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1619
      have b0e7194 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e379 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e379
        | exact resolve b0e379 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e379
      have b0e7417 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e7194 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e7194
        | (have j0 := b0e7194 X0 X1
           grind)
        | exact resolve b0e7194 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7194
      have b0e7852 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e324 X0 X1
           have i₂ := b0e419 X0 X1
           grind)
        | exact superpose b0e419 b0e324
        | (have j0 := b0e324 X0 X1
           have j1 := b0e419 X0 X1
           grind)
        | (have r₁ := b0e324 X0 X1
           have r₂ := b0e419 X0 X1
           grind)
        | exact resolve b0e324 b0e419
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e324 b0e419
      have b0e8029 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e7852 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7852
      have b0e12542 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1641 (τ X1) (τ X0)
           have i₂ := b0e108 X0 X1
           grind)
        | exact superpose b0e108 b0e1641
        | (have j0 := b0e1641 (τ X0) (τ X1)
           grind)
        | exact resolve b0e1641 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1641
      have b0e12634 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12542 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e12542
        | (have j0 := b0e12542 X0 X1
           grind)
        | exact resolve b0e12542 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12542
      have b0e12670 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12634 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e12634
        | (have j0 := b0e12634 X0 X1
           grind)
        | exact resolve b0e12634 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12634
      have b0e12696 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12670 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e12670
        | (have j0 := b0e12670 X0 X1
           grind)
        | exact resolve b0e12670 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12670
      have b0e12715 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12696 X0 X1
           have i₂ := b0e54 X1
           grind)
        | exact superpose b0e54 b0e12696
        | (have j0 := b0e12696 X0 X1
           grind)
        | exact resolve b0e12696 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12696
      have b0e12726 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e12715 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e12715
        | (have j0 := b0e12715 X0 X1
           grind)
        | exact resolve b0e12715 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12715
      have b0e12733 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e12726 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e12726
        | (have j0 := b0e12726 X0 X1
           grind)
        | exact resolve b0e12726 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12726
      have b0e12736 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e12733 X0 X1
           have i₂ := b0e54 X1
           grind)
        | exact superpose b0e54 b0e12733
        | (have j0 := b0e12733 X0 X1
           grind)
        | exact resolve b0e12733 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12733
      have b0e18902 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1479 (τ X0) (τ X1)
           have i₂ := b0e108 X0 X1
           grind)
        | exact superpose b0e108 b0e1479
        | (have j0 := b0e1479 (τ X1) (τ X0)
           grind)
        | exact resolve b0e1479 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1479
      have b0e19022 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e18902 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e18902
        | (have j0 := b0e18902 X0 X1
           grind)
        | exact resolve b0e18902 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18902
      have b0e19067 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e19022 X0 X1
           have i₂ := b0e54 X1
           grind)
        | exact superpose b0e54 b0e19022
        | (have j0 := b0e19022 X0 X1
           grind)
        | exact resolve b0e19022 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19022
      have b0e19101 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e19067 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e19067
        | (have j0 := b0e19067 X0 X1
           grind)
        | exact resolve b0e19067 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19067
      have b0e19128 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e19101 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e19101
        | (have j0 := b0e19101 X0 X1
           grind)
        | exact resolve b0e19101 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19101
      have b0e19153 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e19128 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e19128
        | (have j0 := b0e19128 X0 X1
           grind)
        | exact resolve b0e19128 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19128
      have b0e19175 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e19153 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e19153
        | (have j0 := b0e19153 X0 X1
           grind)
        | exact resolve b0e19153 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19153
      have b0e19184 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e19175 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e19175
        | (have j0 := b0e19175 X0 X1
           grind)
        | exact resolve b0e19175 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19175
      have b0e19193 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e19184 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e19184
        | (have j0 := b0e19184 X0 X1
           grind)
        | exact resolve b0e19184 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19184
      have b0e72503 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 (τ X1)
           have i₂ := b0e8029 X1 (τ X0)
           grind)
        | exact superpose b0e8029 b0e22
        | (have j1 := b0e8029 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e8029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e72841 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 (σ X1)
           have i₂ := b0e8029 (σ X0) X1
           grind)
        | exact superpose b0e8029 b0e35
        | (have j1 := b0e8029 (σ X0) X1
           grind)
        | exact resolve b0e35 b0e8029
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8029
      have b0e73249 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e72841 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e72841
        | (have j0 := b0e72841 X0 X1
           grind)
        | exact resolve b0e72841 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72841
      have b0e73390 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e72503 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e72503
        | (have j0 := b0e72503 X0 X1
           grind)
        | exact resolve b0e72503 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72503
      have b0e73728 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e73249 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e73249
        | (have j0 := b0e73249 X0 X1
           grind)
        | exact resolve b0e73249 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73249
      have b0e73802 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e73390 X0 X1
           have i₂ := b0e54 X0
           grind)
        | exact superpose b0e54 b0e73390
        | (have j0 := b0e73390 X0 X1
           grind)
        | exact resolve b0e73390 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54 b0e73390
      have b0e74017 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e73728 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e73728
        | (have j0 := b0e73728 X0 X1
           grind)
        | exact resolve b0e73728 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73728
      have b0e74070 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e73802 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e73802
        | (have j0 := b0e73802 X0 X1
           grind)
        | exact resolve b0e73802 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73802
      have b0e74211 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e74017 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e74017
        | (have j0 := b0e74017 X0 X1
           grind)
        | exact resolve b0e74017 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74017
      have b0e74254 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e74070 X0 X1
           have i₂ := b0e108 X0 X1
           grind)
        | exact superpose b0e108 b0e74070
        | (have j0 := b0e74070 X0 X1
           grind)
        | exact resolve b0e74070 b0e108
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e74070
      have b0e74312 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e74211 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e74211
        | (have j0 := b0e74211 X0 X1
           grind)
        | exact resolve b0e74211 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74211
      have b0e75794 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 X1
           have i₂ := b0e74312 (σ X0) X1
           grind)
        | exact superpose b0e74312 b0e35
        | (have j1 := b0e74312 (σ X0) X1
           grind)
        | exact resolve b0e35 b0e74312
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74312
      have b0e76149 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e75794 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e75794
        | (have j0 := b0e75794 X0 X1
           grind)
        | exact resolve b0e75794 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75794
      have b0e76840 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e76149 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e76149
        | (have j0 := b0e76149 X0 X1
           grind)
        | exact resolve b0e76149 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76149
      have b0e86858 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e12736 X1 X0
           have i₂ := b0e74254 X0 X1
           grind)
        | exact superpose b0e74254 b0e12736
        | (have j0 := b0e12736 X0 X1
           have j1 := b0e74254 X1 X0
           grind)
        | (have r₁ := b0e12736 X1 X0
           have r₂ := b0e74254 X0 X1
           grind)
        | (have r₁ := b0e12736 X1 X1
           have r₂ := b0e74254 X1 X1
           grind)
        | exact resolve b0e12736 b0e74254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12736
      have b0e87532 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e74254 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74254
      have b0e87588 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e86858 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86858
      have b0e88362 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e87588 X0 X1
           have j1 := b0e87532 X0 X1
           grind)
        | (have r₁ := b0e87588 X0 X1
           have r₂ := b0e87532 X0 X1
           grind)
        | (have r₁ := b0e87588 X1 X0
           have r₂ := b0e87532 X0 X1
           grind)
        | (have r₁ := b0e87588 X1 X1
           have r₂ := b0e87532 X1 X1
           grind)
        | exact resolve b0e87588 b0e87532
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87532 b0e87588
      have b0e113397 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e88362 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e88362
        | (have j0 := b0e88362 (σ X0) X1
           grind)
        | exact resolve b0e88362 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88362
      have b0e113456 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e113397 X0 X1
           have i₂ := b0e35 X0 X1
           grind)
        | exact superpose b0e35 b0e113397
        | (have j0 := b0e113397 X0 X1
           grind)
        | exact resolve b0e113397 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e113397
      have b0e133517 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (σ X1) X0
           have i₂ := b0e76840 X1 (σ X0)
           grind)
        | exact superpose b0e76840 b0e28
        | (have j1 := b0e76840 X1 (σ X0)
           grind)
        | exact resolve b0e28 b0e76840
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76840
      have b0e133528 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e133517 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e133517
        | (have j0 := b0e133517 X0 X1
           grind)
        | exact resolve b0e133517 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133517
      have b0e133566 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e133528 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e133528
        | (have j0 := b0e133528 X0 X1
           grind)
        | exact resolve b0e133528 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133528
      have b0e133596 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e133566 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e133566
        | (have j0 := b0e133566 X0 X1
           grind)
        | exact resolve b0e133566 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133566
      have b0e133617 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e133596 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e133596
        | (have j0 := b0e133596 X0 X1
           grind)
        | exact resolve b0e133596 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133596
      have b0e133629 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e133617 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e133617
        | (have j0 := b0e133617 X0 X1
           grind)
        | exact resolve b0e133617 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133617
      have b0e141509 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e133629 x y
           grind)
        | exact superpose b0e133629 b0e18
        | (have j1 := b0e133629 x y
           grind)
        | exact resolve b0e18 b0e133629
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133629
      have b0e144112 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e141509
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e141509
        | (have j1 := b0e16 y x
           grind)
        | exact resolve b0e141509 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e144117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e141509
           have i₂ := b0e7417 x y
           grind)
        | exact superpose b0e7417 b0e141509
        | (have j1 := b0e7417 x y
           grind)
        | (have r₁ := b0e141509
           have r₂ := b0e7417 x y
           grind)
        | exact resolve b0e141509 b0e7417
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7417 b0e141509
      have b0e144124 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e144117
      have b0e144125 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e144124
      have b0e144130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e144112
      have b0e144131 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e144130
      have b0e144133 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e144125
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e144125 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144125
      have b0e179457 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (σ X1) X0
           have i₂ := b0e113456 X1 (σ X0)
           grind)
        | exact superpose b0e113456 b0e28
        | (have j1 := b0e113456 X1 (σ X0)
           grind)
        | exact resolve b0e28 b0e113456
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e113456
      have b0e179462 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179457 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e179457
        | (have j0 := b0e179457 X0 X1
           grind)
        | exact resolve b0e179457 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179457
      have b0e179475 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179462 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e179462
        | (have j0 := b0e179462 X0 X1
           grind)
        | exact resolve b0e179462 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179462
      have b0e179482 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179475 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e179475
        | (have j0 := b0e179475 X0 X1
           grind)
        | exact resolve b0e179475 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179475
      have b0e179486 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179482 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e179482
        | (have j0 := b0e179482 X0 X1
           grind)
        | exact resolve b0e179482 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179482
      have b0e179487 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e179486 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e179486
        | (have j0 := b0e179486 X0 X1
           grind)
        | exact resolve b0e179486 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179486
      have b0e182524 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e179487 x y
           grind)
        | exact superpose b0e179487 b0e18
        | (have j1 := b0e179487 x y
           grind)
        | exact resolve b0e18 b0e179487
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179487
      have b0e234870 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e195 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e195
        | exact resolve b0e195 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195
      have b0e234922 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e234870 X0 X1
           have i₂ := b0e52 X0
           grind)
        | exact superpose b0e52 b0e234870
        | (have j0 := b0e234870 X0 X1
           grind)
        | exact resolve b0e234870 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52 b0e234870
      have b0e235224 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e182524
           have i₂ := b0e234922 x y
           grind)
        | exact superpose b0e234922 b0e182524
        | (have j1 := b0e234922 x y
           grind)
        | (have r₁ := b0e182524
           have r₂ := b0e234922 x y
           grind)
        | exact resolve b0e182524 b0e234922
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e182524 b0e234922
      have b0e235297 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e235224
      have b0e235298 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e235297
      have b0e235322 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have j1 := b0e19193 y x
           grind)
        | (have r₁ := b0e235298
           have r₂ := b0e19193 y x
           grind)
        | exact resolve b0e235298 b0e19193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19193 b0e235298
      have b0e235454 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e235322
           have i₂ := b0e144133
           grind)
        | exact superpose b0e144133 b0e235322
        | exact resolve b0e235322 b0e144133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144133 b0e235322
      have b0e235486 : (M.op x y) = (M.op y y) ∨ (M.op x x) = (k y x) := by grind
      clear b0e235454
      have b0e235490 : (M.op x x) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e235486
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e235486 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e235486
      have b0e235835 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e1481 x y
           have i₂ := b0e235490
           grind)
        | exact superpose b0e235490 b0e1481
        | (have j0 := b0e1481 x y
           grind)
        | exact resolve b0e1481 b0e235490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1481
      have b0e235836 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e1482 x y
           have i₂ := b0e235490
           grind)
        | exact superpose b0e235490 b0e1482
        | (have j0 := b0e1482 x y
           grind)
        | exact resolve b0e1482 b0e235490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1482
      have b0e235861 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e235836
      have b0e235862 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e235835
      have b0e243816 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e235861
           grind)
        | exact superpose b0e235861 b0e18
        | exact resolve b0e18 b0e235861
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e235861
      have b0e247434 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e243816
           have i₂ := b0e144131
           grind)
        | exact superpose b0e144131 b0e243816
        | exact resolve b0e243816 b0e144131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e243816
      have b0e247436 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e247434
      have b0e251078 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e247436
           grind)
        | exact superpose b0e247436 b0e18
        | exact resolve b0e18 b0e247436
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e251085 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e179 x (σ y)
           have i₂ := b0e247436
           grind)
        | exact superpose b0e247436 b0e179
        | (have j0 := b0e179 x (σ y)
           grind)
        | (have r₁ := b0e179 x (σ y)
           have r₂ := b0e247436
           grind)
        | exact resolve b0e179 b0e247436
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179 b0e247436
      have b0e251094 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e251085
      have b0e251101 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e251094
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e251094
        | exact resolve b0e251094 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e251094
      have b0e251108 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e251101
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e251101
        | exact resolve b0e251101 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e251101
      have b0e251112 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e251108
           have i₂ := b0e235490
           grind)
        | exact superpose b0e235490 b0e251108
        | exact resolve b0e251108 b0e235490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e251108
      have b0e251115 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e251112
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e251112
        | exact resolve b0e251112 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e251112
      have b0e251116 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e251115
      have b0e259177 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e251116
           have i₂ := b0e144131
           grind)
        | exact superpose b0e144131 b0e251116
        | exact resolve b0e251116 b0e144131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e144131 b0e251116
      have b0e259286 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e259177
      have b0e259351 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b0e259286
           have r₂ := b0e251078
           grind)
        | exact resolve b0e259286 b0e251078
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e251078 b0e259286
      have b0e263256 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e259351
           grind)
        | exact superpose b0e259351 b0e15
        | (have j0 := b0e15 x x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e259351
           grind)
        | exact resolve b0e15 b0e259351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e263298 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e263256
      have b0e263303 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
        first
        | (have i₁ := b0e263298
           have i₂ := b0e235490
           grind)
        | exact superpose b0e235490 b0e263298
        | exact resolve b0e263298 b0e235490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e235490 b0e263298
      have b0e263304 : (M.op x x) = (M.op y y) := by grind
      clear b0e263303
      have b0e267261 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e235862
           have i₂ := b0e263304
           grind)
        | exact superpose b0e263304 b0e235862
        | exact resolve b0e235862 b0e263304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e235862 b0e263304
      have b0e267451 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e267261
      have b0e270877 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e267451
           grind)
        | exact superpose b0e267451 b0e18
        | exact resolve b0e18 b0e267451
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e267451
      have b0e270930 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e270877
           have i₂ := b0e259351
           grind)
        | exact superpose b0e259351 b0e270877
        | exact resolve b0e270877 b0e259351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e259351 b0e270877
      have b0e270931 : False := by grind
      exact b0e270931
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e48 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e50 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b1e50
        have b1e54 : (k x y) = (M.op y y) := by grind
        clear b1e48
        have b1e55 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e52 y
             grind)
          | exact superpose b1e52 b1e55
          | exact resolve b1e55 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e52 (σ X0)
             grind)
          | exact superpose b1e52 b1e18
          | exact resolve b1e18 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e58 X0
             have i₂ := b1e52 X0
             grind)
          | exact superpose b1e52 b1e58
          | exact resolve b1e58 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e58
        have b1e71 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e73 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e71 X0
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e71
          | (have j0 := b1e71 X0
             grind)
          | exact resolve b1e71 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e122 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e21
          | exact resolve b1e21 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e126 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e122
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e122
          | exact resolve b1e122 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e605 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e73 (σ x)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e73
          | (have j0 := b1e73 (σ x)
             grind)
          | (have r₁ := b1e73 (σ x)
             have r₂ := b1e56
             grind)
          | exact resolve b1e73 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e73
        have b1e607 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e605
        have b1e608 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e607
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e607
          | exact resolve b1e607 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e607
        have b1e609 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e608
             have r₂ := b1e126
             grind)
          | exact resolve b1e608 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e608
        have b1e610 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e609
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e609
          | exact resolve b1e609 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609
        have b1e611 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e610
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e610
          | exact resolve b1e610 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e610
        have b1e612 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e611
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e611
          | exact resolve b1e611 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e611
        have b1e613 : False := by grind
        exact b1e613
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e47 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : (k x y) = (M.op y y) := by grind
        clear b2e47
        have b2e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e49 (σ X0)
             grind)
          | exact superpose b2e49 b2e18
          | exact resolve b2e18 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e52 X0
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e52
          | exact resolve b2e52 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e52
        have b2e86 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b2e134 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e59 y
             grind)
          | exact superpose b2e59 b2e22
          | exact resolve b2e22 b2e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e957 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e86 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e958 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e957
             have r₂ := b2e21
             grind)
          | exact resolve b2e957 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e957
        have b2e959 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e958
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e958
          | exact resolve b2e958 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e958
        have b2e960 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e959
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e959
          | exact resolve b2e959 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e959
        have b2e961 : False := by grind
        exact b2e961
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : (M.op y x) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e50
        have b3e55 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e53
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e53
          | exact resolve b3e53 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e71 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e15
          | exact resolve b3e15 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e73
        have b3e78 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e77
          | exact resolve b3e77 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e79 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e52 y
             grind)
          | exact superpose b3e52 b3e78
          | exact resolve b3e78 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e79
          | exact resolve b3e79 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e128 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e80
             grind)
          | exact superpose b3e80 b3e13
          | exact resolve b3e13 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e129 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e128
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e128
          | exact resolve b3e128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e231 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e71 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e232 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e231
             have r₂ := b3e20
             grind)
          | exact resolve b3e231 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e231
        have b3e235 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e129
             have i₂ := b3e232
             grind)
          | exact superpose b3e232 b3e129
          | exact resolve b3e129 b3e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129 b3e232
        have b3e240 : False := by grind
        exact b3e240
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e14
            | exact resolve b4e14 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e26 X1 X0
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30
            | exact resolve b4e30 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b4e64
          have b4e70 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e68
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e68
            | exact resolve b4e68 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e72 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e67 y
               grind)
            | exact superpose b4e67 b4e70
            | exact resolve b4e70 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e73 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e72
            | exact resolve b4e72 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e67 (σ X0)
               grind)
            | exact superpose b4e67 b4e19
            | exact resolve b4e19 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e67 (τ X0)
               grind)
            | exact superpose b4e67 b4e26
            | exact resolve b4e26 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e81 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e78 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e78
            | exact resolve b4e78 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e75 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e75
            | exact resolve b4e75 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e87 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e81 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e81
            | exact resolve b4e81 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e81
          have b4e96 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e23
            | exact resolve b4e23 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : (σ (M.op y x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e84 x
               grind)
            | exact superpose b4e84 b4e96
            | exact resolve b4e96 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e116 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e134 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e137 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e124 X0 X1
               have i₂ := b4e84 X1
               grind)
            | exact superpose b4e84 b4e124
            | (have j0 := b4e124 X0 X1
               grind)
            | exact resolve b4e124 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e132 X0 X1
               have j1 := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X0 X1
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X1 X0
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X1 X1
               have r₂ := b4e130 X1 X1
               grind)
            | exact resolve b4e132 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132
          have b4e146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e137
            | (have j0 := b4e137 X0 X1
               grind)
            | exact resolve b4e137 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e186 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e14
            | exact resolve b4e14 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e261 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (τ X0) X1
               have i₂ := b4e186 X0
               grind)
            | exact superpose b4e186 b4e16
            | (have j0 := b4e16 (τ X0) X1
               grind)
            | exact resolve b4e16 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e381 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y x) ∨ (M.op y x) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e130 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e130
            | (have j0 := b4e130 X0 y
               grind)
            | exact resolve b4e130 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e469 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e87 X1
               have i₂ := b4e134 X0 (τ X1)
               grind)
            | exact superpose b4e134 b4e87
            | (have j1 := b4e134 X0 (τ X1)
               grind)
            | exact resolve b4e87 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e479 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e134 (τ X1) X0
               grind)
            | exact superpose b4e134 b4e25
            | (have j1 := b4e134 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e496 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e469 X0 X1
               have i₂ := b4e26 X1 X0
               grind)
            | exact superpose b4e26 b4e469
            | (have j0 := b4e469 X0 X1
               grind)
            | exact resolve b4e469 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e469
          have b4e525 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e496 X0 X1
               have i₂ := b4e186 X1
               grind)
            | exact superpose b4e186 b4e496
            | (have j0 := b4e496 X0 X1
               grind)
            | exact resolve b4e496 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e496
          have b4e625 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e140 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e140
            | (have j0 := b4e140 (σ X1) (σ X0)
               grind)
            | exact resolve b4e140 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e661 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X0 X1
               have i₂ := b4e140 X1 (τ X0)
               grind)
            | exact superpose b4e140 b4e25
            | (have j1 := b4e140 X1 (τ X0)
               grind)
            | exact resolve b4e25 b4e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e140
          have b4e703 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e661 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e661
            | (have j0 := b4e661 X0 X1
               grind)
            | exact resolve b4e661 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e661
          have b4e719 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e625 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e625
            | (have j0 := b4e625 X0 X1
               grind)
            | exact resolve b4e625 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e625
          have b4e736 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e703 X0 X1
               have i₂ := b4e186 X0
               grind)
            | exact superpose b4e186 b4e703
            | (have j0 := b4e703 X0 X1
               grind)
            | exact resolve b4e703 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186 b4e703
          have b4e749 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e719 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e719
            | (have j0 := b4e719 X0 X1
               grind)
            | exact resolve b4e719 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e719
          have b4e2176 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2177 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146
          have b4e10161 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e479 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e479
            | exact resolve b4e479 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e479
          have b4e10451 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e10161 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e10161
            | (have j0 := b4e10161 X0 X1
               grind)
            | exact resolve b4e10161 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10161
          have b4e12138 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (M.op X0 (τ (σ y))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e736 (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e736
            | (have j0 := b4e736 (σ y) X0
               grind)
            | exact resolve b4e736 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e12256 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X1 X1)
               have i₂ := b4e736 X1 X0
               grind)
            | exact superpose b4e736 b4e15
            | (have j1 := b4e736 X1 X0
               grind)
            | exact resolve b4e15 b4e736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e12321 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e261 X0 X1
               have i₂ := b4e736 X0 X1
               grind)
            | exact superpose b4e736 b4e261
            | (have j0 := b4e261 X0 X1
               have j1 := b4e736 X0 X1
               grind)
            | (have r₁ := b4e261 X0 X1
               have r₂ := b4e736 X0 X1
               grind)
            | exact resolve b4e261 b4e736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e261 b4e736
          have b4e12546 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e12321 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12321
          have b4e12702 : ∀ X0 : G, (M.op X0 y) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12138 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e12138
            | (have j0 := b4e12138 X0
               grind)
            | exact resolve b4e12138 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12138
          have b4e12803 : ∀ X0 : G, (M.op X0 y) = (τ (σ (M.op y x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12702 X0
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e12702
            | (have j0 := b4e12702 X0
               grind)
            | exact resolve b4e12702 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12702
          have b4e12865 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12803 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e12803
            | (have j0 := b4e12803 X0
               grind)
            | exact resolve b4e12803 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12803
          have b4e12904 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12865 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e12865
            | (have j0 := b4e12865 X0
               grind)
            | exact resolve b4e12865 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12865
          have b4e12922 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12904 X0
               have i₂ := b4e73
               grind)
            | exact superpose b4e73 b4e12904
            | (have j0 := b4e12904 X0
               grind)
            | exact resolve b4e12904 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e12904
          have b4e12932 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e12922 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e12922
            | (have j0 := b4e12922 X0
               grind)
            | exact resolve b4e12922 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12922
          have b4e21096 : ∀ X0 : G, (k y X0) = (τ (σ (M.op y x))) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e14 (k y X0)
               have i₂ := b4e12932 X0
               grind)
            | exact superpose b4e12932 b4e14
            | (have j1 := b4e12932 X0
               grind)
            | exact resolve b4e14 b4e12932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12932
          have b4e21160 : ∀ X0 : G, (M.op y x) = (k y X0) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e21096 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e21096
            | (have j0 := b4e21096 X0
               grind)
            | exact resolve b4e21096 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21096
          have b4e21531 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e749 X0 X1
               grind)
            | exact superpose b4e749 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e749 X0 X1
               grind)
            | exact resolve b4e17 b4e749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e749
          have b4e21689 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21531 X0 X1
               have i₂ := b4e84 X1
               grind)
            | exact superpose b4e84 b4e21531
            | (have j0 := b4e21531 X0 X1
               grind)
            | exact resolve b4e21531 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21531
          have b4e21848 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21689 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e21689
            | (have j0 := b4e21689 X0 X1
               grind)
            | exact resolve b4e21689 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21689
          have b4e21849 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e21848 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21848
          have b4e21949 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21849 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e21849
            | (have j0 := b4e21849 X0 X1
               grind)
            | exact resolve b4e21849 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21849
          have b4e21990 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21949 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e21949
            | (have j0 := b4e21949 X0 X1
               grind)
            | exact resolve b4e21949 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21949
          have b4e21991 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e21990 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21990
          have b4e22047 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e134 y X0
               have i₂ := b4e21160 X0
               grind)
            | exact superpose b4e21160 b4e134
            | (have j0 := b4e134 y X0
               have j1 := b4e21160 X0
               grind)
            | exact resolve b4e134 b4e21160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134 b4e21160
          have b4e22096 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e22047 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22047
          have b4e22115 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e22096 X0
               have j1 := b4e381 X0
               grind)
            | (have r₁ := b4e22096 y
               have r₂ := b4e381 y
               grind)
            | (have r₁ := b4e22096 X0
               have r₂ := b4e381 X0
               grind)
            | exact resolve b4e22096 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381 b4e22096
          have b4e22522 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e22115 X0
               have i₂ := b4e10451 y X0
               grind)
            | exact superpose b4e10451 b4e22115
            | (have j0 := b4e22115 X0
               have j1 := b4e10451 y X0
               grind)
            | exact resolve b4e22115 b4e10451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10451
          have b4e22692 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e22522 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22522
          have b4e26159 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2176 (τ X1) (τ X0)
               have i₂ := b4e41 X1 X0
               grind)
            | exact superpose b4e41 b4e2176
            | (have j0 := b4e2176 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2176 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2176
          have b4e26301 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26159 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e26159
            | (have j0 := b4e26159 X0 X1
               grind)
            | exact resolve b4e26159 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26159
          have b4e26359 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26301 X0 X1
               have i₂ := b4e87 X1
               grind)
            | exact superpose b4e87 b4e26301
            | (have j0 := b4e26301 X0 X1
               grind)
            | exact resolve b4e26301 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26301
          have b4e26404 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26359 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e26359
            | (have j0 := b4e26359 X0 X1
               grind)
            | exact resolve b4e26359 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26359
          have b4e26436 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26404 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e26404
            | (have j0 := b4e26404 X0 X1
               grind)
            | exact resolve b4e26404 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26404
          have b4e26463 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26436 X0 X1
               have i₂ := b4e87 X1
               grind)
            | exact superpose b4e87 b4e26436
            | (have j0 := b4e26436 X0 X1
               grind)
            | exact resolve b4e26436 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26436
          have b4e26485 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e26463 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e26463
            | (have j0 := b4e26463 X0 X1
               grind)
            | exact resolve b4e26463 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26463
          have b4e26502 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e26485 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e26485
            | (have j0 := b4e26485 X0 X1
               grind)
            | exact resolve b4e26485 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26485
          have b4e26515 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e26502 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e26502
            | (have j0 := b4e26502 X0 X1
               grind)
            | exact resolve b4e26502 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26502
          have b4e26728 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2177 (τ X1) (τ X0)
               have i₂ := b4e41 X1 X0
               grind)
            | exact superpose b4e41 b4e2177
            | (have j0 := b4e2177 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2177 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2177
          have b4e26874 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26728 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e26728
            | (have j0 := b4e26728 X0 X1
               grind)
            | exact resolve b4e26728 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26728
          have b4e26933 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26874 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e26874
            | (have j0 := b4e26874 X0 X1
               grind)
            | exact resolve b4e26874 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26874
          have b4e26976 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26933 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e26933
            | (have j0 := b4e26933 X0 X1
               grind)
            | exact resolve b4e26933 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26933
          have b4e27008 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e26976 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e26976
            | (have j0 := b4e26976 X0 X1
               grind)
            | exact resolve b4e26976 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26976
          have b4e27036 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e27008 X0 X1
               have i₂ := b4e87 X1
               grind)
            | exact superpose b4e87 b4e27008
            | (have j0 := b4e27008 X0 X1
               grind)
            | exact resolve b4e27008 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27008
          have b4e27057 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e27036 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e27036
            | (have j0 := b4e27036 X0 X1
               grind)
            | exact resolve b4e27036 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27036
          have b4e27074 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e27057 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e27057
            | (have j0 := b4e27057 X0 X1
               grind)
            | exact resolve b4e27057 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27057
          have b4e27087 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e27074 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e27074
            | (have j0 := b4e27074 X0 X1
               grind)
            | exact resolve b4e27074 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27074
          have b4e88893 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X0 (τ X1)
               have i₂ := b4e12546 X1 (τ X0)
               grind)
            | exact superpose b4e12546 b4e26
            | (have j1 := b4e12546 X1 (τ X0)
               grind)
            | exact resolve b4e26 b4e12546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e89272 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 (σ X1)
               have i₂ := b4e12546 (σ X0) X1
               grind)
            | exact superpose b4e12546 b4e38
            | (have j1 := b4e12546 (σ X0) X1
               grind)
            | exact resolve b4e38 b4e12546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12546
          have b4e89680 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e89272 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e89272
            | (have j0 := b4e89272 X0 X1
               grind)
            | exact resolve b4e89272 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89272
          have b4e89835 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e88893 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e88893
            | (have j0 := b4e88893 X0 X1
               grind)
            | exact resolve b4e88893 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88893
          have b4e90186 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e89680 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e89680
            | (have j0 := b4e89680 X0 X1
               grind)
            | exact resolve b4e89680 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89680
          have b4e90260 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e89835 X0 X1
               have i₂ := b4e87 X0
               grind)
            | exact superpose b4e87 b4e89835
            | (have j0 := b4e89835 X0 X1
               grind)
            | exact resolve b4e89835 b4e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87 b4e89835
          have b4e90475 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e90186 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e90186
            | (have j0 := b4e90186 X0 X1
               grind)
            | exact resolve b4e90186 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90186
          have b4e90536 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e90260 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e90260
            | (have j0 := b4e90260 X0 X1
               grind)
            | exact resolve b4e90260 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90260
          have b4e90683 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e90475 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e90475
            | (have j0 := b4e90475 X0 X1
               grind)
            | exact resolve b4e90475 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90475
          have b4e90732 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e90536 X0 X1
               have i₂ := b4e41 X0 X1
               grind)
            | exact superpose b4e41 b4e90536
            | (have j0 := b4e90536 X0 X1
               grind)
            | exact resolve b4e90536 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e90536
          have b4e90794 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e90683 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e90683
            | (have j0 := b4e90683 X0 X1
               grind)
            | exact resolve b4e90683 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90683
          have b4e92494 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 X1
               have i₂ := b4e90794 (σ X0) X1
               grind)
            | exact superpose b4e90794 b4e38
            | (have j1 := b4e90794 (σ X0) X1
               grind)
            | exact resolve b4e38 b4e90794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e92620 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e90794 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90794
          have b4e92874 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e92494 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e92494
            | (have j0 := b4e92494 X0 X1
               grind)
            | exact resolve b4e92494 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92494
          have b4e93625 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e92874 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e92874
            | (have j0 := b4e92874 X0 X1
               grind)
            | exact resolve b4e92874 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92874
          have b4e94622 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e92620 y X0
               have i₂ := b4e22692 X0
               grind)
            | (have i₁ := b4e92620 X0 X0
               have i₂ := b4e22692 X0
               grind)
            | exact superpose b4e22692 b4e92620
            | (have j0 := b4e92620 y X0
               have j1 := b4e22692 X0
               grind)
            | (have r₁ := b4e92620 y y
               have r₂ := b4e22692 y
               grind)
            | (have r₁ := b4e92620 y X0
               have r₂ := b4e22692 X0
               grind)
            | (have r₁ := b4e92620 x y
               have r₂ := b4e22692 y
               grind)
            | exact resolve b4e92620 b4e22692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22692 b4e92620
          have b4e94727 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e94622 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94622
          have b4e94873 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have j0 := b4e94727 X0
               have j1 := b4e65 X0
               grind)
            | (have r₁ := b4e94727 X0
               have r₂ := b4e65 X0
               grind)
            | exact resolve b4e94727 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94727
          have b4e94953 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y x) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e94873 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e94873
            | (have j0 := b4e94873 X0
               grind)
            | exact resolve b4e94873 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94873
          have b4e118935 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e26515 X1 X0
               have i₂ := b4e90732 X0 X1
               grind)
            | exact superpose b4e90732 b4e26515
            | (have j0 := b4e26515 X1 X0
               have j1 := b4e90732 X0 X1
               grind)
            | (have r₁ := b4e26515 X1 X1
               have r₂ := b4e90732 X1 X1
               grind)
            | (have r₁ := b4e26515 X1 X0
               have r₂ := b4e90732 X0 X1
               grind)
            | exact resolve b4e26515 b4e90732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26515 b4e90732
          have b4e118957 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e118935 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118935
          have b4e119021 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e118957 X0 X1
               have j1 := b4e27087 X1 X0
               grind)
            | (have r₁ := b4e118957 X1 X0
               have r₂ := b4e27087 X0 X1
               grind)
            | exact resolve b4e118957 b4e27087
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27087 b4e118957
          have b4e147293 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e119021 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e119021 X0 X1
               grind)
            | exact superpose b4e119021 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e119021 X1 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e119021 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e119021 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X0
               have r₂ := b4e119021 X0 X1
               grind)
            | exact resolve b4e16 b4e119021
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119021
          have b4e147302 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e147293 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147293
          have b4e168005 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e147302 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e147302
            | (have j0 := b4e147302 (σ X0) (σ X1)
               grind)
            | exact resolve b4e147302 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147302
          have b4e168071 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e168005 X0 X1
               have i₂ := b4e84 X1
               grind)
            | exact superpose b4e84 b4e168005
            | (have j0 := b4e168005 X0 X1
               grind)
            | exact resolve b4e168005 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168005
          have b4e168093 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e168071 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e168071
            | (have j0 := b4e168071 X0 X1
               grind)
            | exact resolve b4e168071 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168071
          have b4e168100 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e168093 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e168093
            | (have j0 := b4e168093 X0 X1
               grind)
            | exact resolve b4e168093 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168093
          have b4e168104 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e168100 X0 X1
               have i₂ := b4e14 (k X0 X1)
               grind)
            | exact superpose b4e14 b4e168100
            | (have j0 := b4e168100 X0 X1
               grind)
            | exact resolve b4e168100 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168100
          have b4e168107 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e168104 X0 X1
               have i₂ := b4e84 X1
               grind)
            | exact superpose b4e84 b4e168104
            | (have j0 := b4e168104 X0 X1
               grind)
            | exact resolve b4e168104 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168104
          have b4e210220 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (σ X1) X0
               have i₂ := b4e93625 X1 (σ X0)
               grind)
            | exact superpose b4e93625 b4e30
            | (have j1 := b4e93625 X1 (σ X0)
               grind)
            | exact resolve b4e30 b4e93625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e93625
          have b4e210231 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e210220 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e210220
            | (have j0 := b4e210220 X0 X1
               grind)
            | exact resolve b4e210220 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210220
          have b4e210269 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e210231 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e210231
            | (have j0 := b4e210231 X0 X1
               grind)
            | exact resolve b4e210231 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210231
          have b4e210299 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e210269 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e210269
            | (have j0 := b4e210269 X0 X1
               grind)
            | exact resolve b4e210269 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210269
          have b4e210320 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e210299 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e210299
            | (have j0 := b4e210299 X0 X1
               grind)
            | exact resolve b4e210299 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210299
          have b4e210332 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e210320 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e210320
            | (have j0 := b4e210320 X0 X1
               grind)
            | exact resolve b4e210320 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210320
          have b4e226966 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e210332 x y
               grind)
            | exact superpose b4e210332 b4e20
            | (have j1 := b4e210332 x y
               grind)
            | exact resolve b4e20 b4e210332
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e210332
          have b4e227089 : (M.op y x) = (k y x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e226966
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e226966
            | exact resolve b4e226966 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226966
          have b4e227124 : (M.op y x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e94953 x
               grind)
            | (have r₁ := b4e227089
               have r₂ := b4e94953 x
               grind)
            | exact resolve b4e227089 b4e94953
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94953 b4e227089
          have b4e227655 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e22115 x
               have i₂ := b4e227124
               grind)
            | exact superpose b4e227124 b4e22115
            | (have j0 := b4e22115 x
               grind)
            | exact resolve b4e22115 b4e227124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22115
          have b4e227701 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e227655
          have b4e227728 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have j1 := b4e65 x
               grind)
            | (have r₁ := b4e227701
               have r₂ := b4e65 x
               grind)
            | exact resolve b4e227701 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227701
          have b4e592963 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e15 (M.op X0 X0)
               have i₂ := b4e525 X1 X0
               grind)
            | exact superpose b4e525 b4e15
            | (have j1 := b4e525 X1 X0
               grind)
            | exact resolve b4e15 b4e525
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e525
          have b4e669453 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e12256 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e12256
            | (have j0 := b4e12256 X1 (σ X0)
               grind)
            | exact resolve b4e12256 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12256
          have b4e669469 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e669453 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e669453
            | (have j0 := b4e669453 X0 X1
               grind)
            | exact resolve b4e669453 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669453
          have b4e669472 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e669469 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e669469
            | (have j0 := b4e669469 X0 X1
               grind)
            | exact resolve b4e669469 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669469
          have b4e669475 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e669472 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e669472
            | (have j0 := b4e669472 X0 X1
               grind)
            | exact resolve b4e669472 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669472
          have b4e678779 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e669475 y x
               have i₂ := b4e227728
               grind)
            | exact superpose b4e227728 b4e669475
            | (have j0 := b4e669475 y x
               grind)
            | exact resolve b4e669475 b4e227728
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227728 b4e669475
          have b4e678805 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e678779
          have b4e678825 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e678805
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e678805
            | exact resolve b4e678805 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e678805
          have b4e678831 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b4e678825
               have r₂ := b4e100
               grind)
            | exact resolve b4e678825 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e678825
          have b4e678833 : (σ (M.op x y)) = (σ (M.op y x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e678831
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e678831
            | exact resolve b4e678831 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e678831
          have b4e1599507 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e592963 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e592963
            | (have j0 := b4e592963 (σ X0) X1
               grind)
            | exact resolve b4e592963 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e592963
          have b4e1599512 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1599507 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e1599507
            | (have j0 := b4e1599507 X0 X1
               grind)
            | exact resolve b4e1599507 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1599507
          have b4e1599513 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1599512 X0 X1
               have i₂ := b4e84 X0
               grind)
            | exact superpose b4e84 b4e1599512
            | (have j0 := b4e1599512 X0 X1
               grind)
            | exact resolve b4e1599512 b4e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e84 b4e1599512
          have b4e1599514 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1599513 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e1599513
            | (have j0 := b4e1599513 X0 X1
               grind)
            | exact resolve b4e1599513 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1599513
          have b4e2940638 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (σ (M.op x x)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e168107 y x
               grind)
            | exact superpose b4e168107 b4e20
            | (have j1 := b4e168107 y x
               grind)
            | exact resolve b4e20 b4e168107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e168107
          have b4e2940645 : (σ (M.op x x)) = (σ (k y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e1599514 x y
               grind)
            | (have r₁ := b4e2940638
               have r₂ := b4e1599514 x y
               grind)
            | exact resolve b4e2940638 b4e1599514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1599514 b4e2940638
          have b4e2940651 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e2940645
               have i₂ := b4e227124
               grind)
            | exact superpose b4e227124 b4e2940645
            | exact resolve b4e2940645 b4e227124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e227124 b4e2940645
          have b4e2940694 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e65 x
               grind)
            | (have r₁ := b4e2940651
               have r₂ := b4e65 x
               grind)
            | exact resolve b4e2940651 b4e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65 b4e2940651
          have b4e2940695 : (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e2940694
               have r₂ := b4e100
               grind)
            | exact resolve b4e2940694 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940694
          have b4e2940734 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e21991 y x
               have i₂ := b4e2940695
               grind)
            | exact superpose b4e2940695 b4e21991
            | (have j0 := b4e21991 y x
               grind)
            | exact resolve b4e21991 b4e2940695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21991
          have b4e2940771 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b4e2940734
          have b4e2940801 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2940771
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2940771
            | exact resolve b4e2940771 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940771
          have b4e2940836 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e2940801
               have r₂ := b4e100
               grind)
            | exact resolve b4e2940801 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100 b4e2940801
          have b4e2940851 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e2940836
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2940836
            | exact resolve b4e2940836 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940836
          have b4e2940869 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e2940851
               grind)
            | exact superpose b4e2940851 b4e20
            | exact resolve b4e20 b4e2940851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940851
          have b4e2940949 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e2940869
               have i₂ := b4e678833
               grind)
            | exact superpose b4e678833 b4e2940869
            | (have r₁ := b4e2940869
               have r₂ := b4e678833
               grind)
            | exact resolve b4e2940869 b4e678833
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e678833 b4e2940869
          have b4e2940958 : (M.op x y) = (M.op x x) := by grind
          clear b4e2940949
          have b4e2940969 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e2940958
               grind)
            | exact superpose b4e2940958 b4e17
            | (have j0 := b4e17 x x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e2940958
               grind)
            | exact resolve b4e17 b4e2940958
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940958
          have b4e2940996 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
          clear b4e2940969
          have b4e2941005 : (M.op x x) = (M.op y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e2940996
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2940996
            | exact resolve b4e2940996 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940996
          have b4e2941006 : (M.op y y) = (k y x) := by
            first
            | (have r₁ := b4e2941005
               have r₂ := b4e21
               grind)
            | exact resolve b4e2941005 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2941005
          have b4e2941007 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b4e2941006
               have i₂ := b4e2940695
               grind)
            | exact superpose b4e2940695 b4e2941006
            | exact resolve b4e2941006 b4e2940695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2940695 b4e2941006
          have b4e2941009 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b4e22
               have i₂ := b4e2941007
               grind)
            | exact superpose b4e2941007 b4e22
            | exact resolve b4e22 b4e2941007
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2941007
          have b4e2941413 : False := by grind
          exact b4e2941413
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e68
            | exact resolve b5e68 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e68
          have b5e85 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e120 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e219 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e220 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e219
               have r₂ := b5e21
               grind)
            | exact resolve b5e219 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e219
          have b5e1165 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1166 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1165
               have r₂ := b5e23
               grind)
            | exact resolve b5e1165 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1165
          have b5e1167 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1166
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1166
            | exact resolve b5e1166 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1166
          have b5e1168 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1167
               have i₂ := b5e220
               grind)
            | exact superpose b5e220 b5e1167
            | exact resolve b5e1167 b5e220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e220 b5e1167
          have b5e1172 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1168
               grind)
            | exact superpose b5e1168 b5e23
            | exact resolve b5e23 b5e1168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1168
          have b5e1181 : False := by grind
          exact b5e1181
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e48 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e48
        have b6e51 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e50
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e50
          | exact resolve b6e50 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e67 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e15
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e71 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e67
        have b6e72 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e71
          | exact resolve b6e71 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e73 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e49 y
             grind)
          | exact superpose b6e49 b6e72
          | exact resolve b6e72 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e72
        have b6e122 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e73
             grind)
          | exact superpose b6e73 b6e13
          | exact resolve b6e13 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e123 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e122
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e122
          | exact resolve b6e122 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e141 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e123
             grind)
          | exact superpose b6e123 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e142 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e141
        have b6e144 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e142
             have r₂ := b6e21
             grind)
          | exact resolve b6e142 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e146 : False := by grind
        exact b6e146
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e62 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e62
          have b7e66 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e64 y
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e64 (σ X0)
               grind)
            | exact superpose b7e64 b7e19
            | exact resolve b7e19 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e69 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e69
            | exact resolve b7e69 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e69
          have b7e86 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e86 X0
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e86
            | (have j0 := b7e86 X0
               grind)
            | exact resolve b7e86 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e23
            | exact resolve b7e23 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e93 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e89
            | exact resolve b7e89 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e656 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e88 (σ x)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e88
            | (have j0 := b7e88 (σ x)
               grind)
            | (have r₁ := b7e88 (σ x)
               have r₂ := b7e67
               grind)
            | exact resolve b7e88 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e88
          have b7e658 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e656
          have b7e659 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e658
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e658
            | exact resolve b7e658 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e658
          have b7e660 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e659
               have r₂ := b7e93
               grind)
            | exact resolve b7e659 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e659
          have b7e661 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e660
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e660
            | exact resolve b7e660 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e660
          have b7e662 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e661
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e661
            | exact resolve b7e661 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e661
          have b7e664 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e662
               have i₂ := b7e127 x y
               grind)
            | exact superpose b7e127 b7e662
            | (have j1 := b7e127 x y
               grind)
            | exact resolve b7e662 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e666 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e662
               grind)
            | exact superpose b7e662 b7e14
            | exact resolve b7e14 b7e662
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e662
          have b7e689 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e666
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e666
            | exact resolve b7e666 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e666
          have b7e691 : (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e664
               have r₂ := b7e93
               grind)
            | exact resolve b7e664 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e664
          have b7e694 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e691
               have r₂ := b7e22
               grind)
            | exact resolve b7e691 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e691
          have b7e695 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e694
               have i₂ := b7e689
               grind)
            | exact superpose b7e689 b7e694
            | exact resolve b7e694 b7e689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e689 b7e694
          have b7e696 : False := by grind
          exact b7e696
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e26 X1 X0
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e30
            | exact resolve b8e30 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e61 (σ X0)
               grind)
            | exact superpose b8e61 b8e19
            | exact resolve b8e19 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e66 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e61 (τ X0)
               grind)
            | exact superpose b8e61 b8e26
            | exact resolve b8e26 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e69 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e66 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e66
            | exact resolve b8e66 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e63 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e63
            | exact resolve b8e63 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e75 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e69 X0
               have i₂ := b8e61 X0
               grind)
            | exact superpose b8e61 b8e69
            | exact resolve b8e69 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61 b8e69
          have b8e88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e16
            | (have j0 := b8e16 (σ X0) X1
               grind)
            | exact resolve b8e16 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e106 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e128 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e115 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e115
            | (have j0 := b8e115 X0 X1
               grind)
            | exact resolve b8e115 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e130 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               have j1 := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X0 X1
               have r₂ := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X0
               have r₂ := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X1
               have r₂ := b8e121 X1 X1
               grind)
            | exact resolve b8e123 b8e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121 b8e123
          have b8e133 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e128 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e128
            | (have j0 := b8e128 X0 X1
               grind)
            | exact resolve b8e128 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e14
            | exact resolve b8e14 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e205 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (τ X0) X1
               have i₂ := b8e145 X0
               grind)
            | exact superpose b8e145 b8e16
            | (have j0 := b8e16 (τ X0) X1
               grind)
            | exact resolve b8e16 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e367 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e130 X1 (τ X0)
               grind)
            | exact superpose b8e130 b8e25
            | (have j1 := b8e130 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e382 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e130 (τ X0) X1
               grind)
            | exact superpose b8e130 b8e26
            | (have j1 := b8e130 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e398 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e367 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e367
            | (have j0 := b8e367 X0 X1
               grind)
            | exact resolve b8e367 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e421 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X1
               have i₂ := b8e145 X0
               grind)
            | exact superpose b8e145 b8e398
            | (have j0 := b8e398 X0 X1
               grind)
            | exact resolve b8e398 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145 b8e398
          have b8e1351 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e133 X1 X0
               grind)
            | exact superpose b8e133 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e133 X1 X0
               grind)
            | exact resolve b8e16 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1368 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1369 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1370 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e1415 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1351 X0 X1
               have j1 := b8e88 X0 (σ X1)
               grind)
            | (have r₁ := b8e1351 X0 X0
               have r₂ := b8e88 X0 (σ X0)
               grind)
            | (have r₁ := b8e1351 X0 X1
               have r₂ := b8e88 X0 (σ X1)
               grind)
            | exact resolve b8e1351 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88 b8e1351
          have b8e1469 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1415 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e1415
            | (have j0 := b8e1415 X0 X1
               grind)
            | exact resolve b8e1415 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1415
          have b8e1505 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1469 X0 X1
               have i₂ := b8e72 X1
               grind)
            | exact superpose b8e72 b8e1469
            | (have j0 := b8e1469 X0 X1
               grind)
            | exact resolve b8e1469 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1469
          have b8e1527 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1505 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1505
            | (have j0 := b8e1505 X0 X1
               grind)
            | exact resolve b8e1505 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1505
          have b8e5312 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e382 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e382
            | exact resolve b8e382 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e382
          have b8e5511 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e5312 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e5312
            | (have j0 := b8e5312 X0 X1
               grind)
            | exact resolve b8e5312 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5312
          have b8e5827 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e205 X0 X1
               have i₂ := b8e421 X0 X1
               grind)
            | exact superpose b8e421 b8e205
            | (have j0 := b8e205 X0 X1
               have j1 := b8e421 X0 X1
               grind)
            | (have r₁ := b8e205 X0 X1
               have r₂ := b8e421 X0 X1
               grind)
            | exact resolve b8e205 b8e421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205 b8e421
          have b8e5977 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e5827 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5827
          have b8e10394 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1527 (τ X1) (τ X0)
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e1527
            | (have j0 := b8e1527 (τ X0) (τ X1)
               grind)
            | exact resolve b8e1527 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1527
          have b8e10476 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10394 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e10394
            | (have j0 := b8e10394 X0 X1
               grind)
            | exact resolve b8e10394 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10394
          have b8e10506 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10476 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e10476
            | (have j0 := b8e10476 X0 X1
               grind)
            | exact resolve b8e10476 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10476
          have b8e10527 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10506 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e10506
            | (have j0 := b8e10506 X0 X1
               grind)
            | exact resolve b8e10506 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10506
          have b8e10542 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10527 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e10527
            | (have j0 := b8e10527 X0 X1
               grind)
            | exact resolve b8e10527 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10527
          have b8e10551 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10542 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e10542
            | (have j0 := b8e10542 X0 X1
               grind)
            | exact resolve b8e10542 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10542
          have b8e10556 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10551 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e10551
            | (have j0 := b8e10551 X0 X1
               grind)
            | exact resolve b8e10551 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10551
          have b8e10557 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10556 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e10556
            | (have j0 := b8e10556 X0 X1
               grind)
            | exact resolve b8e10556 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10556
          have b8e17666 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1369 (τ X1) (τ X0)
               have i₂ := b8e40 X1 X0
               grind)
            | exact superpose b8e40 b8e1369
            | (have j0 := b8e1369 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1369 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1369
          have b8e17775 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17666 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e17666
            | (have j0 := b8e17666 X0 X1
               grind)
            | exact resolve b8e17666 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17666
          have b8e17822 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17775 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e17775
            | (have j0 := b8e17775 X0 X1
               grind)
            | exact resolve b8e17775 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17775
          have b8e17858 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17822 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e17822
            | (have j0 := b8e17822 X0 X1
               grind)
            | exact resolve b8e17822 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17822
          have b8e17887 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17858 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e17858
            | (have j0 := b8e17858 X0 X1
               grind)
            | exact resolve b8e17858 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17858
          have b8e17912 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17887 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e17887
            | (have j0 := b8e17887 X0 X1
               grind)
            | exact resolve b8e17887 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17887
          have b8e17935 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17912 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e17912
            | (have j0 := b8e17912 X0 X1
               grind)
            | exact resolve b8e17912 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17912
          have b8e17952 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17935 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e17935
            | (have j0 := b8e17935 X0 X1
               grind)
            | exact resolve b8e17935 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17935
          have b8e17965 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17952 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e17952
            | (have j0 := b8e17952 X0 X1
               grind)
            | exact resolve b8e17952 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17952
          have b8e18252 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1370 (τ X1) (τ X0)
               have i₂ := b8e40 X1 X0
               grind)
            | exact superpose b8e40 b8e1370
            | (have j0 := b8e1370 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1370 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1370
          have b8e18362 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18252 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e18252
            | (have j0 := b8e18252 X0 X1
               grind)
            | exact resolve b8e18252 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18252
          have b8e18406 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18362 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e18362
            | (have j0 := b8e18362 X0 X1
               grind)
            | exact resolve b8e18362 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18362
          have b8e18442 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18406 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e18406
            | (have j0 := b8e18406 X0 X1
               grind)
            | exact resolve b8e18406 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18406
          have b8e18471 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18442 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e18442
            | (have j0 := b8e18442 X0 X1
               grind)
            | exact resolve b8e18442 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18442
          have b8e18496 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18471 X0 X1
               have i₂ := b8e75 X1
               grind)
            | exact superpose b8e75 b8e18471
            | (have j0 := b8e18471 X0 X1
               grind)
            | exact resolve b8e18471 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18471
          have b8e18517 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e18496 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e18496
            | (have j0 := b8e18496 X0 X1
               grind)
            | exact resolve b8e18496 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18496
          have b8e18534 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e18517 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e18517
            | (have j0 := b8e18517 X0 X1
               grind)
            | exact resolve b8e18517 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18517
          have b8e18547 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e18534 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e18534
            | (have j0 := b8e18534 X0 X1
               grind)
            | exact resolve b8e18534 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18534
          have b8e79560 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 (τ X1)
               have i₂ := b8e5977 X1 (τ X0)
               grind)
            | exact superpose b8e5977 b8e26
            | (have j1 := b8e5977 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e5977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e79925 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 (σ X1)
               have i₂ := b8e5977 (σ X0) X1
               grind)
            | exact superpose b8e5977 b8e37
            | (have j1 := b8e5977 (σ X0) X1
               grind)
            | exact resolve b8e37 b8e5977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5977
          have b8e80342 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e79925 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e79925
            | (have j0 := b8e79925 X0 X1
               grind)
            | exact resolve b8e79925 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79925
          have b8e80490 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e79560 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e79560
            | (have j0 := b8e79560 X0 X1
               grind)
            | exact resolve b8e79560 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79560
          have b8e80846 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e80342 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e80342
            | (have j0 := b8e80342 X0 X1
               grind)
            | exact resolve b8e80342 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80342
          have b8e80926 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e80490 X0 X1
               have i₂ := b8e75 X0
               grind)
            | exact superpose b8e75 b8e80490
            | (have j0 := b8e80490 X0 X1
               grind)
            | exact resolve b8e80490 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e80490
          have b8e81147 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e80846 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e80846
            | (have j0 := b8e80846 X0 X1
               grind)
            | exact resolve b8e80846 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80846
          have b8e81207 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e80926 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e80926
            | (have j0 := b8e80926 X0 X1
               grind)
            | exact resolve b8e80926 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80926
          have b8e81351 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e81147 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e81147
            | (have j0 := b8e81147 X0 X1
               grind)
            | exact resolve b8e81147 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81147
          have b8e81399 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e81207 X0 X1
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e81207
            | (have j0 := b8e81207 X0 X1
               grind)
            | exact resolve b8e81207 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e81207
          have b8e81458 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e81351 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e81351
            | (have j0 := b8e81351 X0 X1
               grind)
            | exact resolve b8e81351 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81351
          have b8e82990 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 X1
               have i₂ := b8e81458 (σ X0) X1
               grind)
            | exact superpose b8e81458 b8e37
            | (have j1 := b8e81458 (σ X0) X1
               grind)
            | exact resolve b8e37 b8e81458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81458
          have b8e83353 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e82990 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e82990
            | (have j0 := b8e82990 X0 X1
               grind)
            | exact resolve b8e82990 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82990
          have b8e84084 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e83353 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e83353
            | (have j0 := b8e83353 X0 X1
               grind)
            | exact resolve b8e83353 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83353
          have b8e99185 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10557 X1 X0
               have i₂ := b8e81399 X0 X1
               grind)
            | exact superpose b8e81399 b8e10557
            | (have j0 := b8e10557 X0 X1
               have j1 := b8e81399 X1 X0
               grind)
            | (have r₁ := b8e10557 X1 X0
               have r₂ := b8e81399 X0 X1
               grind)
            | (have r₁ := b8e10557 X1 X1
               have r₂ := b8e81399 X1 X1
               grind)
            | exact resolve b8e10557 b8e81399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99276 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17965 X1 X0
               have i₂ := b8e81399 X0 X1
               grind)
            | exact superpose b8e81399 b8e17965
            | (have j0 := b8e17965 X1 X0
               have j1 := b8e81399 X0 X1
               grind)
            | (have r₁ := b8e17965 X1 X1
               have r₂ := b8e81399 X1 X1
               grind)
            | (have r₁ := b8e17965 X1 X0
               have r₂ := b8e81399 X0 X1
               grind)
            | exact resolve b8e17965 b8e81399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17965
          have b8e99296 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e81399 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99297 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e81399 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81399
          have b8e99298 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e99276 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99276
          have b8e99312 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e99185 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99185
          have b8e99382 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e99298 X0 X1
               have j1 := b8e18547 X1 X0
               grind)
            | (have r₁ := b8e99298 X1 X0
               have r₂ := b8e18547 X0 X1
               grind)
            | exact resolve b8e99298 b8e18547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18547 b8e99298
          have b8e99419 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e99312 X0 X1
               have j1 := b8e99296 X0 X1
               grind)
            | (have r₁ := b8e99312 X0 X1
               have r₂ := b8e99296 X0 X1
               grind)
            | (have r₁ := b8e99312 X1 X0
               have r₂ := b8e99296 X0 X1
               grind)
            | (have r₁ := b8e99312 X1 X1
               have r₂ := b8e99296 X1 X1
               grind)
            | exact resolve b8e99312 b8e99296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99296 b8e99312
          have b8e112286 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e99382 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e99382 X0 X1
               grind)
            | exact superpose b8e99382 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e99382 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e99382 X1 X1
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e99382 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e99382 X0 X0
               grind)
            | exact resolve b8e17 b8e99382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99382
          have b8e112354 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e112286 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112286
          have b8e112369 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e112354 X0 X1
               have j1 := b8e99297 X1 X0
               grind)
            | (have r₁ := b8e112354 X0 X1
               have r₂ := b8e99297 X0 X1
               grind)
            | (have r₁ := b8e112354 X1 X0
               have r₂ := b8e99297 X0 X1
               grind)
            | (have r₁ := b8e112354 X1 X1
               have r₂ := b8e99297 X1 X1
               grind)
            | exact resolve b8e112354 b8e99297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99297 b8e112354
          have b8e113710 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e99419 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e99419
            | (have j0 := b8e99419 (σ X0) X1
               grind)
            | exact resolve b8e99419 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99419
          have b8e113852 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e113710 X0 X1
               have i₂ := b8e37 X0 X1
               grind)
            | exact superpose b8e37 b8e113710
            | (have j0 := b8e113710 X0 X1
               grind)
            | exact resolve b8e113710 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113710
          have b8e124687 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e112369 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e112369
            | (have j0 := b8e112369 (σ X0) X1
               grind)
            | exact resolve b8e112369 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112369
          have b8e124757 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e124687 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e124687
            | (have j0 := b8e124687 X0 X1
               grind)
            | exact resolve b8e124687 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124687
          have b8e147718 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e84084 X1 (σ X0)
               grind)
            | exact superpose b8e84084 b8e30
            | (have j1 := b8e84084 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e84084
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84084
          have b8e147729 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e147718 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e147718
            | (have j0 := b8e147718 X0 X1
               grind)
            | exact resolve b8e147718 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147718
          have b8e147767 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e147729 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e147729
            | (have j0 := b8e147729 X0 X1
               grind)
            | exact resolve b8e147729 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147729
          have b8e147797 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e147767 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e147767
            | (have j0 := b8e147767 X0 X1
               grind)
            | exact resolve b8e147767 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147767
          have b8e147818 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e147797 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e147797
            | (have j0 := b8e147797 X0 X1
               grind)
            | exact resolve b8e147797 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147797
          have b8e147830 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e147818 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e147818
            | (have j0 := b8e147818 X0 X1
               grind)
            | exact resolve b8e147818 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147818
          have b8e152738 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e147830 x y
               grind)
            | exact superpose b8e147830 b8e20
            | (have j1 := b8e147830 x y
               grind)
            | exact resolve b8e20 b8e147830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147830
          have b8e153872 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e152738
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e152738
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e152738 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e153877 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e152738
               have i₂ := b8e5511 x y
               grind)
            | exact superpose b8e5511 b8e152738
            | (have j1 := b8e5511 x y
               grind)
            | (have r₁ := b8e152738
               have r₂ := b8e5511 x y
               grind)
            | exact resolve b8e152738 b8e5511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5511 b8e152738
          have b8e153884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e153877
          have b8e153885 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e153884
          have b8e153890 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e153872
          have b8e153891 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e153890
          have b8e153893 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e153885
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e153885 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153885
          have b8e159472 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e10557 y x
               have i₂ := b8e153893
               grind)
            | exact superpose b8e153893 b8e10557
            | (have j0 := b8e10557 y x
               grind)
            | (have r₁ := b8e10557 y x
               have r₂ := b8e153893
               grind)
            | exact resolve b8e10557 b8e153893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10557
          have b8e159488 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
          clear b8e153893
          have b8e159492 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e159472
          have b8e159507 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e159492
               have r₂ := b8e159488
               grind)
            | exact resolve b8e159492 b8e159488
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159488 b8e159492
          have b8e212084 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e113852 X1 (σ X0)
               grind)
            | exact superpose b8e113852 b8e30
            | (have j1 := b8e113852 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e113852
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e113852
          have b8e212089 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e212084 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e212084
            | (have j0 := b8e212084 X0 X1
               grind)
            | exact resolve b8e212084 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212084
          have b8e212102 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e212089 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e212089
            | (have j0 := b8e212089 X0 X1
               grind)
            | exact resolve b8e212089 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212089
          have b8e212109 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e212102 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e212102
            | (have j0 := b8e212102 X0 X1
               grind)
            | exact resolve b8e212102 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212102
          have b8e212113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e212109 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e212109
            | (have j0 := b8e212109 X0 X1
               grind)
            | exact resolve b8e212109 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212109
          have b8e212114 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e212113 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e212113
            | (have j0 := b8e212113 X0 X1
               grind)
            | exact resolve b8e212113 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212113
          have b8e215906 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e212114 x y
               grind)
            | exact superpose b8e212114 b8e20
            | (have j1 := b8e212114 x y
               grind)
            | exact resolve b8e20 b8e212114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e212114
          have b8e238329 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 (σ X1)
               have i₂ := b8e124757 X1 (σ X0)
               grind)
            | exact superpose b8e124757 b8e37
            | (have j1 := b8e124757 X1 (σ X0)
               grind)
            | exact resolve b8e37 b8e124757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37 b8e124757
          have b8e238334 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e238329 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e238329
            | (have j0 := b8e238329 X0 X1
               grind)
            | exact resolve b8e238329 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238329
          have b8e238351 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e238334 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e238334
            | (have j0 := b8e238334 X0 X1
               grind)
            | exact resolve b8e238334 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238334
          have b8e238362 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e238351 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e238351
            | (have j0 := b8e238351 X0 X1
               grind)
            | exact resolve b8e238351 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238351
          have b8e238368 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e238362 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e238362
            | (have j0 := b8e238362 X0 X1
               grind)
            | exact resolve b8e238362 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238362
          have b8e238369 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e238368 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e238368
            | (have j0 := b8e238368 X0 X1
               grind)
            | exact resolve b8e238368 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e238368
          have b8e246365 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e238369 y x
               grind)
            | exact superpose b8e238369 b8e20
            | (have j1 := b8e238369 y x
               grind)
            | exact resolve b8e20 b8e238369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e238369
          have b8e250291 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e246365
               have i₂ := b8e153891
               grind)
            | exact superpose b8e153891 b8e246365
            | exact resolve b8e246365 b8e153891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153891 b8e246365
          have b8e250292 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e250291
          have b8e250293 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e250292
          have b8e253663 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e159507
               have i₂ := b8e250293
               grind)
            | exact superpose b8e250293 b8e159507
            | exact resolve b8e159507 b8e250293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159507 b8e250293
          have b8e253692 : (M.op x y) = (M.op x x) := by grind
          clear b8e253663
          have b8e257213 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e215906
               have i₂ := b8e253692
               grind)
            | exact superpose b8e253692 b8e215906
            | exact resolve b8e215906 b8e253692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e215906
          have b8e257215 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e253692
               grind)
            | exact superpose b8e253692 b8e17
            | (have j0 := b8e17 x x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e253692
               grind)
            | exact resolve b8e17 b8e253692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e257257 : (M.op y y) = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
          clear b8e257215
          have b8e257258 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e257213
          have b8e257259 : (M.op x x) = (k y x) := by grind
          clear b8e257258
          have b8e260877 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e1368 x y
               have i₂ := b8e257259
               grind)
            | exact superpose b8e257259 b8e1368
            | (have j0 := b8e1368 x y
               grind)
            | exact resolve b8e1368 b8e257259
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1368
          have b8e260905 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e260877
          have b8e264854 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b8e257259
               have i₂ := b8e257257
               grind)
            | exact superpose b8e257257 b8e257259
            | exact resolve b8e257259 b8e257257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e257257 b8e257259
          have b8e264904 : (M.op x x) = (M.op y y) := by grind
          clear b8e264854
          have b8e271184 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e260905
               have i₂ := b8e264904
               grind)
            | exact superpose b8e264904 b8e260905
            | exact resolve b8e260905 b8e264904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e260905 b8e264904
          have b8e271186 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e271184
          have b8e272920 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e271186
               grind)
            | exact superpose b8e271186 b8e20
            | exact resolve b8e20 b8e271186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271186
          have b8e272972 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e272920
               have i₂ := b8e253692
               grind)
            | exact superpose b8e253692 b8e272920
            | exact resolve b8e272920 b8e253692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253692 b8e272920
          have b8e272973 : False := by grind
          exact b8e272973

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation2301 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ a ∨ k a b = b :=
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
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b1e42 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e45 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e42
        have b1e46 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e23
             grind)
          | exact resolve b1e45 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e46
          | exact resolve b1e46 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e47
          | exact resolve b1e47 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e47
        have b1e49 : False := by grind
        exact b1e49
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
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e137 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e622 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e137 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e137
          | (have j0 := b2e137 x y
             grind)
          | exact resolve b2e137 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e137
        have b2e628 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e622
        have b2e634 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e628
             have r₂ := b2e22
             grind)
          | exact resolve b2e628 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e628
        have b2e640 : False := by grind
        exact b2e640
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
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
        have b3e42 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e44 : x = y ∨ y = (k x y) := by grind
        clear b3e42
        have b3e45 : y = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e23
             grind)
          | exact resolve b3e44 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e44
        have b3e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e29
          | exact resolve b3e29 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e45
        have b3e49 : False := by grind
        exact b3e49
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e41 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e44 : x = y ∨ y = (k x y) := by grind
          clear b5e41
          have b5e46 : y = (k x y) := by
            first
            | (have r₁ := b5e44
               have r₂ := b5e25
               grind)
            | exact resolve b5e44 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e44
          have b5e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e154 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e512 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e154 x y
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e154
            | (have j0 := b5e154 x y
               grind)
            | exact resolve b5e154 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e154
          have b5e515 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e512
          have b5e518 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e515
               have r₂ := b5e24
               grind)
            | exact resolve b5e515 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e515
          have b5e522 : False := by grind
          exact b5e522
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
        have b6e47 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e49 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e47
        have b6e52 : y = (M.op x y) := by
          first
          | (have r₁ := b6e49
             have r₂ := b6e21
             grind)
          | exact resolve b6e49 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e55 : False := by grind
        exact b6e55
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
          have b7e37 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e25
               grind)
            | exact resolve b7e39 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e39
          have b7e41 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : y = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e56 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e55
          have b7e58 : x = (M.op x y) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e21
               grind)
            | exact resolve b7e56 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : False := by grind
          exact b7e60
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e20
            | (have j1 := b8e43 x y
               grind)
            | exact resolve b8e20 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e113
               have r₂ := b8e24
               grind)
            | exact resolve b8e113 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e126 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e123
               have r₂ := b8e23
               grind)
            | exact resolve b8e123 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e126
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e126
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e126 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126
          have b8e128 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e127
          have b8e129 : y = (M.op x y) := by
            first
            | (have r₁ := b8e128
               have r₂ := b8e22
               grind)
            | exact resolve b8e128 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e130 : False := by grind
          exact b8e130

/-- `Equation2301`: `x = (y ◇ (x ◇ (y ◇ x))) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation2301 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2301 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2301.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
      have b0e51 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
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
      have b0e52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e57 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e162 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e52 x y
           grind)
        | exact superpose b0e52 b0e18
        | (have j1 := b0e52 x y
           grind)
        | exact resolve b0e18 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e169 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e52 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e170 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e52 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e400 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e51 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e51
        | exact resolve b0e51 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e433 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e400 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e400
        | (have j0 := b0e400 X0 X1
           grind)
        | exact resolve b0e400 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e400
      have b0e729 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e169 (τ X1) (τ X0)
           have i₂ := b0e57 X1 X0
           grind)
        | exact superpose b0e57 b0e169
        | (have j0 := b0e169 (τ X1) (τ X0)
           grind)
        | exact resolve b0e169 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e746 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e729 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e729
        | (have j0 := b0e729 X0 X1
           grind)
        | exact resolve b0e729 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e729
      have b0e752 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e746 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e746
        | (have j0 := b0e746 X0 X1
           grind)
        | exact resolve b0e746 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e746
      have b0e757 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e752 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e752
        | (have j0 := b0e752 X0 X1
           grind)
        | exact resolve b0e752 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e752
      have b0e761 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e757 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e757
        | (have j0 := b0e757 X0 X1
           grind)
        | exact resolve b0e757 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e757
      have b0e765 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e761 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e761
        | (have j0 := b0e761 X0 X1
           grind)
        | exact resolve b0e761 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e761
      have b0e767 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e765 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e765
        | (have j0 := b0e765 X0 X1
           grind)
        | exact resolve b0e765 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e765
      have b0e785 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e170 (τ X1) (τ X0)
           have i₂ := b0e57 X1 X0
           grind)
        | exact superpose b0e57 b0e170
        | (have j0 := b0e170 (τ X1) (τ X0)
           grind)
        | exact resolve b0e170 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e800 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e785 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e785
        | (have j0 := b0e785 X0 X1
           grind)
        | exact resolve b0e785 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e785
      have b0e806 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e800 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e800
        | (have j0 := b0e800 X0 X1
           grind)
        | exact resolve b0e800 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e800
      have b0e811 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e806 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e806
        | (have j0 := b0e806 X0 X1
           grind)
        | exact resolve b0e806 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e806
      have b0e815 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e811 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e811
        | (have j0 := b0e811 X0 X1
           grind)
        | exact resolve b0e811 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e811
      have b0e818 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e815 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e815
        | (have j0 := b0e815 X0 X1
           grind)
        | exact resolve b0e815 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e815
      have b0e819 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e818 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e818
        | (have j0 := b0e818 X0 X1
           grind)
        | exact resolve b0e818 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e818
      have b0e847 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e162
           have i₂ := b0e433 x y
           grind)
        | exact superpose b0e433 b0e162
        | (have j1 := b0e433 (σ x) (σ y)
           grind)
        | (have r₁ := b0e162
           have r₂ := b0e433 x y
           grind)
        | exact resolve b0e162 b0e433
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e162 b0e433
      have b0e848 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e847
      have b0e43729 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e848
           grind)
        | exact superpose b0e848 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e848
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e848
           grind)
        | exact resolve b0e14 b0e848
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e848
      have b0e43740 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e43729
      have b0e43744 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e43740
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e43740
        | exact resolve b0e43740 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43740
      have b0e45158 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e43744
           grind)
        | exact superpose b0e43744 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e43744
           grind)
        | exact resolve b0e14 b0e43744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45159 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e43744
           grind)
        | exact superpose b0e43744 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e43744
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e43744
           grind)
        | exact resolve b0e15 b0e43744
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43744
      have b0e45169 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e45159
      have b0e45181 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e45169
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e45169
        | exact resolve b0e45169 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45169
      have b0e45182 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e45158
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e45158
        | exact resolve b0e45158 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45158
      have b0e45183 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e45182
      have b0e141106 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e45181
           grind)
        | exact superpose b0e45181 b0e12
        | exact resolve b0e12 b0e45181
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45181
      have b0e141147 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e141106
           have r₂ := b0e45183
           grind)
        | exact resolve b0e141106 b0e45183
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45183 b0e141106
      have b0e141165 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e141147
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e141147
        | exact resolve b0e141147 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141147
      have b0e141166 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e819 y x
           grind)
        | (have r₁ := b0e141165
           have r₂ := b0e819 y x
           grind)
        | exact resolve b0e141165 b0e819
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e819 b0e141165
      have b0e141332 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e141166
           grind)
        | exact superpose b0e141166 b0e12
        | exact resolve b0e12 b0e141166
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141166
      have b0e141507 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e141332
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e141332
        | exact resolve b0e141332 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141332
      have b0e141508 : y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e767 y x
           grind)
        | (have r₁ := b0e141507
           have r₂ := b0e767 y x
           grind)
        | exact resolve b0e141507 b0e767
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e767 b0e141507
      have b0e141654 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e141508
           grind)
        | exact superpose b0e141508 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e141508
           grind)
        | exact resolve b0e14 b0e141508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e141669 : x ≠ y ∨ x = (M.op x y) := by grind
      have b0e141670 : x = (k y x) ∨ x = (M.op x y) := by grind
      clear b0e141654
      have b0e141974 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e169 x y
           have i₂ := b0e141670
           grind)
        | exact superpose b0e141670 b0e169
        | (have j0 := b0e169 x y
           grind)
        | exact resolve b0e169 b0e141670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e169
      have b0e142205 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e141974
      have b0e145968 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e142205
           grind)
        | exact superpose b0e142205 b0e18
        | exact resolve b0e18 b0e142205
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142205
      have b0e146287 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e145968
           have i₂ := b0e141508
           grind)
        | exact superpose b0e141508 b0e145968
        | exact resolve b0e145968 b0e141508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e145968
      have b0e146290 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
      clear b0e146287
      have b0e146291 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e146290
           have r₂ := b0e141669
           grind)
        | exact resolve b0e146290 b0e141669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146290
      have b0e146447 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e146291
           grind)
        | exact superpose b0e146291 b0e18
        | exact resolve b0e18 b0e146291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e146450 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e146291
           grind)
        | exact superpose b0e146291 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e146291
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e146291
           grind)
        | exact resolve b0e15 b0e146291
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146291
      have b0e146464 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e146450
      have b0e146480 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e146464
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e146464
        | exact resolve b0e146464 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146464
      have b0e146646 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e146447
           have i₂ := b0e141508
           grind)
        | exact superpose b0e141508 b0e146447
        | exact resolve b0e146447 b0e141508
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141508 b0e146447
      have b0e146650 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e146646
           have r₂ := b0e141669
           grind)
        | exact resolve b0e146646 b0e141669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141669 b0e146646
      have b0e147174 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e146480
           have i₂ := b0e141670
           grind)
        | exact superpose b0e141670 b0e146480
        | exact resolve b0e146480 b0e141670
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141670 b0e146480
      have b0e147322 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
      clear b0e147174
      have b0e147420 : x = (M.op x y) := by
        first
        | (have r₁ := b0e147322
           have r₂ := b0e146650
           grind)
        | exact resolve b0e147322 b0e146650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146650 b0e147322
      have b0e147650 : x ≠ y ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e147420
           grind)
        | exact superpose b0e147420 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e147420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e147651 : x ≠ x ∨ x = y ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e147420
           grind)
        | exact superpose b0e147420 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e147420
           grind)
        | exact resolve b0e15 b0e147420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e147668 : y = (k y x) ∨ x = y := by grind
      clear b0e147651
      have b0e148228 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e170 x y
           have i₂ := b0e147668
           grind)
        | exact superpose b0e147668 b0e170
        | (have j0 := b0e170 x y
           grind)
        | exact resolve b0e170 b0e147668
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e170
      have b0e148347 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e148228
      have b0e152998 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e148347
           grind)
        | exact superpose b0e148347 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e148347
           grind)
        | exact resolve b0e14 b0e148347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148347
      have b0e153001 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e152998
      have b0e153002 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e153001
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e153001
        | exact resolve b0e153001 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153001
      have b0e153309 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e153002
           grind)
        | exact superpose b0e153002 b0e18
        | exact resolve b0e18 b0e153002
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153002
      have b0e153326 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e153309
           have i₂ := b0e147420
           grind)
        | exact superpose b0e147420 b0e153309
        | exact resolve b0e153309 b0e147420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153309
      have b0e153327 : (σ x) = (σ (k y x)) ∨ x = y := by grind
      clear b0e153326
      have b0e153490 : (k y x) = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e153327
           grind)
        | exact superpose b0e153327 b0e12
        | exact resolve b0e12 b0e153327
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153327
      have b0e153652 : x = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e153490
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e153490
        | exact resolve b0e153490 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153490
      have b0e153653 : x = (k y x) := by
        first
        | (have r₁ := b0e153652
           have r₂ := b0e147650
           grind)
        | exact resolve b0e153652 b0e147650
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147650 b0e153652
      have b0e153776 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e147668
           have i₂ := b0e153653
           grind)
        | exact superpose b0e153653 b0e147668
        | exact resolve b0e147668 b0e153653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147668 b0e153653
      have b0e153902 : x = y := by grind
      clear b0e153776
      have b0e154036 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e153902
           grind)
        | exact superpose b0e153902 b0e18
        | exact resolve b0e18 b0e153902
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e154038 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e153902
           grind)
        | exact superpose b0e153902 b0e20
        | exact resolve b0e20 b0e153902
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e154105 : x = (M.op x x) := by
        first
        | (have i₁ := b0e147420
           have i₂ := b0e153902
           grind)
        | exact superpose b0e153902 b0e147420
        | exact resolve b0e147420 b0e153902
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147420 b0e153902
      have b0e154168 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e154036
           have i₂ := b0e154105
           grind)
        | exact superpose b0e154105 b0e154036
        | exact resolve b0e154036 b0e154105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e154036 b0e154105
      have b0e154176 : False := by grind
      exact b0e154176
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : x ≠ x ∨ y = (k x y) := by
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
        have b1e26 : y = (k x y) := by grind
        clear b1e24
        have b1e36 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e39 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e36
        have b1e40 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e39
             have r₂ := b1e23
             grind)
          | exact resolve b1e39 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e41
          | exact resolve b1e41 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e41
        have b1e43 : False := by grind
        exact b1e43
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : x ≠ x ∨ y = (k x y) := by
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
        have b2e24 : y = (k x y) := by grind
        clear b2e23
        have b2e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e41 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e569 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e122 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e122
          | (have j0 := b2e122 y x
             grind)
          | exact resolve b2e122 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e122
        have b2e574 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e569
        have b2e579 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e574
             have r₂ := b2e22
             grind)
          | exact resolve b2e574 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e574
        have b2e584 : False := by grind
        exact b2e584
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b3e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e25
        have b3e27 : (σ y) = (σ (k x y)) := by
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
        have b3e28 : (k x y) = (τ (σ y)) := by
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
        have b3e29 : y = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e48 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e51 : x = y ∨ x = (k x y) := by grind
        clear b3e48
        have b3e53 : x = (k x y) := by
          first
          | (have r₁ := b3e51
             have r₂ := b3e23
             grind)
          | exact resolve b3e51 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X0 (M.op X1 X0))) X1) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b4e31 : x = (M.op (M.op y (M.op x y)) y) := by
            first
            | (have i₁ := b4e13 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : (σ x) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
            first
            | (have i₁ := b4e13 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : y = (M.op (M.op (M.op y (M.op x y)) (M.op y x)) (M.op y (M.op x y))) := by
            first
            | (have i₁ := b4e13 y (M.op y (M.op x y))
               have i₂ := b4e31
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : y = (M.op (M.op (M.op y (M.op x y)) y) (M.op y (M.op x y))) := by
            first
            | (have i₁ := b4e35
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e38 : y = (M.op x (M.op y (M.op x y))) := by
            first
            | (have i₁ := b4e37
               have i₂ := b4e31
               grind)
            | exact superpose b4e31 b4e37
            | exact resolve b4e37 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e37
          have b4e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e64 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e75 : (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) (M.op (σ y) (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b4e13 (σ y) (M.op (σ y) (M.op (σ x) (σ y)))
               have i₂ := b4e32
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : (σ y) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e75
            | exact resolve b4e75 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e79 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e32
               grind)
            | exact superpose b4e32 b4e77
            | exact resolve b4e77 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e77
          have b4e80 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e64 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e64
            | exact resolve b4e64 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b4e175 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e196 : (σ y) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (k (M.op (σ y) (M.op (σ x) (σ y))) (σ x)) := by
            first
            | (have i₁ := b4e16 (M.op (σ y) (M.op (σ x) (σ y))) (σ x)
               have i₂ := b4e79
               grind)
            | exact superpose b4e79 b4e16
            | (have j0 := b4e16 (M.op (σ y) (M.op (σ x) (σ y))) (σ x)
               grind)
            | exact resolve b4e16 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e533 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e175 (τ X1) (τ X0)
               have i₂ := b4e80 X1 X0
               grind)
            | exact superpose b4e80 b4e175
            | (have j0 := b4e175 (τ X1) (τ X0)
               grind)
            | exact resolve b4e175 b4e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e542 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e533 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e533
            | (have j0 := b4e533 X0 X1
               grind)
            | exact resolve b4e533 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533
          have b4e545 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e542 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e542
            | (have j0 := b4e542 X0 X1
               grind)
            | exact resolve b4e542 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e542
          have b4e547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e545 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e545
            | (have j0 := b4e545 X0 X1
               grind)
            | exact resolve b4e545 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545
          have b4e548 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e547 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e547
            | (have j0 := b4e547 X0 X1
               grind)
            | exact resolve b4e547 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e547
          have b4e549 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e548 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e548
            | (have j0 := b4e548 X0 X1
               grind)
            | exact resolve b4e548 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e548
          have b4e550 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e549 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e549
            | (have j0 := b4e549 X0 X1
               grind)
            | exact resolve b4e549 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e549
          have b4e608 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e169
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e169
            | (have j1 := b4e18 (σ y) (σ x)
               grind)
            | exact resolve b4e169 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e609 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e608
          have b4e4725 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e609
               grind)
            | exact superpose b4e609 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e609
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e609
               grind)
            | exact resolve b4e16 b4e609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609
          have b4e4734 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e4725
          have b4e4736 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e4734
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e4734
            | exact resolve b4e4734 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4734
          have b4e25871 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (k (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e196
               have i₂ := b4e4736
               grind)
            | exact superpose b4e4736 b4e196
            | exact resolve b4e196 b4e4736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e196 b4e4736
          have b4e25907 : (σ x) = (k (M.op (σ y) (σ x)) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e25871
               have r₂ := b4e24
               grind)
            | exact resolve b4e25871 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25871
          have b4e25919 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e25907
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e25907
            | exact resolve b4e25907 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25907
          have b4e25926 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e25919
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e25919
            | exact resolve b4e25919 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25919
          have b4e25927 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e25926
          have b4e26193 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e25927
               grind)
            | exact superpose b4e25927 b4e14
            | exact resolve b4e14 b4e25927
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25927
          have b4e26353 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e26193
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e26193
            | exact resolve b4e26193 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26193
          have b4e26354 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e550 y x
               grind)
            | (have r₁ := b4e26353
               have r₂ := b4e550 y x
               grind)
            | exact resolve b4e26353 b4e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e550 b4e26353
          have b4e26659 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e26354
               grind)
            | exact superpose b4e26354 b4e16
            | (have j0 := b4e16 y x
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e26354
               grind)
            | exact resolve b4e16 b4e26354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26669 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e26659
          have b4e26973 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e175 x y
               have i₂ := b4e26669
               grind)
            | exact superpose b4e26669 b4e175
            | (have j0 := b4e175 x y
               grind)
            | exact resolve b4e175 b4e26669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e175
          have b4e27020 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e26973
          have b4e37776 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e27020
               grind)
            | exact superpose b4e27020 b4e20
            | exact resolve b4e20 b4e27020
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27020
          have b4e38139 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e37776
               have i₂ := b4e26354
               grind)
            | exact superpose b4e26354 b4e37776
            | exact resolve b4e37776 b4e26354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26354 b4e37776
          have b4e38142 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e38139
          have b4e38143 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e38142
               have r₂ := b4e26
               grind)
            | exact resolve b4e38142 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38142
          have b4e38559 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e38143
               grind)
            | exact superpose b4e38143 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e38143
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e38143
               grind)
            | exact resolve b4e17 b4e38143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38143
          have b4e38568 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e38559
          have b4e38579 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e38568
               have r₂ := b4e25
               grind)
            | exact resolve b4e38568 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38568
          have b4e38595 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e38579
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38579
            | exact resolve b4e38579 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38579
          have b4e39811 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e38595
               have i₂ := b4e26669
               grind)
            | exact superpose b4e26669 b4e38595
            | exact resolve b4e38595 b4e26669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26669 b4e38595
          have b4e40019 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e39811
          have b4e40077 : x = (M.op x y) := by
            first
            | (have r₁ := b4e40019
               have r₂ := b4e25
               grind)
            | exact resolve b4e40019 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e40019
          have b4e40573 : y = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e40077
               grind)
            | exact superpose b4e40077 b4e38
            | exact resolve b4e38 b4e40077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e40609 : y = (M.op x y) := by
            first
            | (have i₁ := b4e40573
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40573
            | exact resolve b4e40573 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40573
          have b4e40623 : x = y := by
            first
            | (have i₁ := b4e40609
               have i₂ := b4e40077
               grind)
            | exact superpose b4e40077 b4e40609
            | exact resolve b4e40609 b4e40077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40077 b4e40609
          have b4e40631 : False := by grind
          exact b4e40631
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e36 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e39 : x = y ∨ x = (k x y) := by grind
          clear b5e36
          have b5e41 : x = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e25
               grind)
            | exact resolve b5e39 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e39
          have b5e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e145 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e44 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e512 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e145 y x
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e145
            | (have j0 := b5e145 y x
               grind)
            | exact resolve b5e145 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e145
          have b5e515 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e512
          have b5e518 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e515
               have r₂ := b5e24
               grind)
            | exact resolve b5e515 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e515
          have b5e522 : False := by grind
          exact b5e522
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e23
        have b6e25 : (σ y) = (σ (k x y)) := by
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
        have b6e26 : (k x y) = (τ (σ y)) := by
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
        have b6e27 : y = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e66 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
        have b6e68 : y = (M.op y x) ∨ x = (M.op y x) := by grind
        clear b6e66
        have b6e71 : x = (M.op y x) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e21
             grind)
          | exact resolve b6e68 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e74 : False := by grind
        exact b6e74
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e25
               grind)
            | exact resolve b7e38 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e38
          have b7e40 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e39
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e39
            | exact resolve b7e39 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e43 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e40
               grind)
            | exact superpose b7e40 b7e14
            | exact resolve b7e14 b7e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e44 : x = (k x y) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e43
            | exact resolve b7e43 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b7e54
          have b7e57 : y = (M.op y x) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e21
               grind)
            | exact resolve b7e55 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e59 : False := by grind
          exact b7e59
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
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
          have b8e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e46 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e32
            | exact resolve b8e32 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e115 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e43 x y
               grind)
            | exact superpose b8e43 b8e20
            | (have j1 := b8e43 x y
               grind)
            | exact resolve b8e20 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e122 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e381 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e121 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e121
            | (have j0 := b8e121 (τ X1) (τ X0)
               grind)
            | exact resolve b8e121 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e389 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e381 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e381
            | (have j0 := b8e381 X0 X1
               grind)
            | exact resolve b8e381 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e381
          have b8e392 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e389 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e389
            | (have j0 := b8e389 X0 X1
               grind)
            | exact resolve b8e389 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e389
          have b8e394 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e392
            | (have j0 := b8e392 X0 X1
               grind)
            | exact resolve b8e392 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e392
          have b8e395 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e394 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e394
            | (have j0 := b8e394 X0 X1
               grind)
            | exact resolve b8e394 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e394
          have b8e396 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e395 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e395
            | (have j0 := b8e395 X0 X1
               grind)
            | exact resolve b8e395 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e395
          have b8e397 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e396 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e396
            | (have j0 := b8e396 X0 X1
               grind)
            | exact resolve b8e396 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e396
          have b8e450 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e122 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e122
            | (have j0 := b8e122 (τ X1) (τ X0)
               grind)
            | exact resolve b8e122 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e457 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e450 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e450
            | (have j0 := b8e450 X0 X1
               grind)
            | exact resolve b8e450 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e450
          have b8e460 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e457 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e457
            | (have j0 := b8e457 X0 X1
               grind)
            | exact resolve b8e457 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e457
          have b8e462 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e460 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e460
            | (have j0 := b8e460 X0 X1
               grind)
            | exact resolve b8e460 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e463 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e462 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e462
            | (have j0 := b8e462 X0 X1
               grind)
            | exact resolve b8e462 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e462
          have b8e464 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e463 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e463
            | (have j0 := b8e463 X0 X1
               grind)
            | exact resolve b8e463 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463
          have b8e465 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e464 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e464
            | (have j0 := b8e464 X0 X1
               grind)
            | exact resolve b8e464 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e464
          have b8e476 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e115
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e115
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e115 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e477 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e476
          have b8e3300 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e477
               grind)
            | exact superpose b8e477 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e477
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e477
               grind)
            | exact resolve b8e16 b8e477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e477
          have b8e3309 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e3300
          have b8e3311 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3309
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3309
            | exact resolve b8e3309 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3309
          have b8e22502 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3311
               grind)
            | exact superpose b8e3311 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3311
               grind)
            | exact resolve b8e16 b8e3311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e22503 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e3311
               grind)
            | exact superpose b8e3311 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e3311
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3311
               grind)
            | exact resolve b8e17 b8e3311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3311
          have b8e22512 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e22503
          have b8e22515 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e22512
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e22512
            | exact resolve b8e22512 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22512
          have b8e22516 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e22502
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e22502
            | exact resolve b8e22502 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22502
          have b8e22517 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e22516
          have b8e154504 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e22515
               grind)
            | exact superpose b8e22515 b8e14
            | exact resolve b8e14 b8e22515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22515
          have b8e154545 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e154504
               have r₂ := b8e22517
               grind)
            | exact resolve b8e154504 b8e22517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22517 b8e154504
          have b8e154563 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e154545
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e154545
            | exact resolve b8e154545 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154545
          have b8e154564 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b8e465 y x
               grind)
            | (have r₁ := b8e154563
               have r₂ := b8e465 y x
               grind)
            | exact resolve b8e154563 b8e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e465 b8e154563
          have b8e154862 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e154564
               grind)
            | exact superpose b8e154564 b8e14
            | exact resolve b8e14 b8e154564
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154564
          have b8e155040 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e154862
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e154862
            | exact resolve b8e154862 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154862
          have b8e155041 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e397 y x
               grind)
            | (have r₁ := b8e155040
               have r₂ := b8e397 y x
               grind)
            | exact resolve b8e155040 b8e397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e397 b8e155040
          have b8e155133 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e155041
               grind)
            | exact superpose b8e155041 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e155041
               grind)
            | exact resolve b8e16 b8e155041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e155146 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e155147 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e155133
          have b8e155689 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e121 x y
               have i₂ := b8e155147
               grind)
            | exact superpose b8e155147 b8e121
            | (have j0 := b8e121 x y
               grind)
            | exact resolve b8e121 b8e155147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121
          have b8e155896 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e155689
          have b8e160252 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e155896
               grind)
            | exact superpose b8e155896 b8e20
            | exact resolve b8e20 b8e155896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155896
          have b8e160539 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e160252
               have i₂ := b8e155041
               grind)
            | exact superpose b8e155041 b8e160252
            | exact resolve b8e160252 b8e155041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160252
          have b8e160542 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e160539
          have b8e160543 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e160542
               have r₂ := b8e155146
               grind)
            | exact resolve b8e160542 b8e155146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160542
          have b8e160747 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e160543
               grind)
            | exact superpose b8e160543 b8e20
            | exact resolve b8e20 b8e160543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e160750 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e160543
               grind)
            | exact superpose b8e160543 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e160543
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e160543
               grind)
            | exact resolve b8e17 b8e160543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160543
          have b8e160762 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e160750
          have b8e160765 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e160762
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e160762
            | exact resolve b8e160762 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160762
          have b8e160845 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e160747
               have i₂ := b8e155041
               grind)
            | exact superpose b8e155041 b8e160747
            | exact resolve b8e160747 b8e155041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155041 b8e160747
          have b8e160849 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e160845
               have r₂ := b8e155146
               grind)
            | exact resolve b8e160845 b8e155146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155146 b8e160845
          have b8e161192 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e160765
               have i₂ := b8e155147
               grind)
            | exact superpose b8e155147 b8e160765
            | exact resolve b8e160765 b8e155147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155147 b8e160765
          have b8e161343 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e161192
          have b8e161444 : x = (M.op x y) := by
            first
            | (have r₁ := b8e161343
               have r₂ := b8e160849
               grind)
            | exact resolve b8e161343 b8e160849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e160849 b8e161343
          have b8e161650 : x ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e161444
               grind)
            | exact superpose b8e161444 b8e16
            | (have j0 := b8e16 y x
               grind)
            | exact resolve b8e16 b8e161444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e161651 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e161444
               grind)
            | exact superpose b8e161444 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e161444
               grind)
            | exact resolve b8e17 b8e161444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e161666 : y = (k y x) ∨ x = y := by grind
          clear b8e161651
          have b8e161968 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e122 x y
               have i₂ := b8e161666
               grind)
            | exact superpose b8e161666 b8e122
            | (have j0 := b8e122 x y
               grind)
            | exact resolve b8e122 b8e161666
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e162075 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e161968
          have b8e164735 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e162075
               grind)
            | exact superpose b8e162075 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e162075
               grind)
            | exact resolve b8e16 b8e162075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162075
          have b8e164740 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e164735
          have b8e164743 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e164740
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e164740
            | exact resolve b8e164740 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164740
          have b8e165115 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e164743
               grind)
            | exact superpose b8e164743 b8e20
            | exact resolve b8e20 b8e164743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164743
          have b8e165129 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e165115
               have i₂ := b8e161444
               grind)
            | exact superpose b8e161444 b8e165115
            | exact resolve b8e165115 b8e161444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165115
          have b8e165130 : (σ x) = (σ (k y x)) ∨ x = y := by grind
          clear b8e165129
          have b8e165341 : (k y x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e165130
               grind)
            | exact superpose b8e165130 b8e14
            | exact resolve b8e14 b8e165130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165130
          have b8e165513 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e165341
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e165341
            | exact resolve b8e165341 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165341
          have b8e165514 : x = (k y x) := by
            first
            | (have r₁ := b8e165513
               have r₂ := b8e161650
               grind)
            | exact resolve b8e165513 b8e161650
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161650 b8e165513
          have b8e165685 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e161666
               have i₂ := b8e165514
               grind)
            | exact superpose b8e165514 b8e161666
            | exact resolve b8e161666 b8e165514
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161666 b8e165514
          have b8e165800 : x = y := by grind
          clear b8e165685
          have b8e165974 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e165800
               grind)
            | exact superpose b8e165800 b8e22
            | exact resolve b8e22 b8e165800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e166011 : x = (M.op x x) := by
            first
            | (have i₁ := b8e161444
               have i₂ := b8e165800
               grind)
            | exact superpose b8e165800 b8e161444
            | exact resolve b8e161444 b8e165800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161444 b8e165800
          have b8e166051 : False := by grind
          exact b8e166051
