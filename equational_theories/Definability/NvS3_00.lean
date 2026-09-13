import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1276`: `x = y ◇ (((x ◇ x) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1276 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1276 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1276.models_iff G M).mp hM
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
      have b0e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      clear b0e41 b0e47
      have b0e173 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e52 x
           grind)
        | exact superpose b0e52 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e52 x
           grind)
        | exact resolve b0e22 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e52
      have b0e187 : False := by grind
      exact b0e187
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
        have b1e49 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        clear b1e49
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
        have b1e71 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e73 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e125 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
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
        have b1e527 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e528 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e527
        have b1e529 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e528
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e528
          | exact resolve b1e528 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e528
        have b1e531 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e529
             have r₂ := b1e125
             grind)
          | exact resolve b1e529 b1e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e529
        have b1e533 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e531
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e531
          | exact resolve b1e531 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e531
        have b1e535 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e533
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e533
          | exact resolve b1e533 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e533
        have b1e537 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e535
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e535
          | exact resolve b1e535 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e535
        have b1e538 : False := by grind
        exact b1e538
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
        have b2e88 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e143 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
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
        have b2e666 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e88 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88
        have b2e667 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e666
             have r₂ := b2e21
             grind)
          | exact resolve b2e666 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e666
        have b2e669 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e667
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e667
          | exact resolve b2e667 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e667
        have b2e671 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e669
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e669
          | exact resolve b2e669 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e669
        have b2e672 : False := by grind
        exact b2e672
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
        have b3e71 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
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
        have b3e80 : (σ (M.op x y)) = (σ (k x y)) := by
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
        have b3e195 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
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
        have b3e211 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e71 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e212 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e211
             have r₂ := b3e20
             grind)
          | exact resolve b3e211 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e218 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e212
             grind)
          | exact superpose b3e212 b3e80
          | exact resolve b3e80 b3e212
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e212
        have b3e222 : False := by grind
        exact b3e222
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
          have b4e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
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
          have b4e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e66
          have b4e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
          have b4e72 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e67 y
               grind)
            | exact superpose b4e67 b4e70
            | exact resolve b4e70 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e70
          have b4e73 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
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
          have b4e74 : False := by grind
          exact b4e74
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
          have b5e122 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e256 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e257 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e256
               have r₂ := b5e21
               grind)
            | exact resolve b5e256 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e256
          have b5e978 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e122 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e122
          have b5e979 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e978
               have r₂ := b5e23
               grind)
            | exact resolve b5e978 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e978
          have b5e981 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e979
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e979
            | exact resolve b5e979 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e979
          have b5e983 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e981
               have i₂ := b5e257
               grind)
            | exact superpose b5e257 b5e981
            | exact resolve b5e981 b5e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e257 b5e981
          have b5e989 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e983
               grind)
            | exact superpose b5e983 b5e23
            | exact resolve b5e23 b5e983
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e983
          have b5e997 : False := by grind
          exact b5e997
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
        have b6e71 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e70
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
        have b6e126 : (k x y) = (τ (σ (M.op y y))) := by
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
        have b6e127 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e126
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e126
          | exact resolve b6e126 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e150 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e127
             grind)
          | exact superpose b6e127 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127
        have b6e151 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e150
        have b6e153 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e151
             have r₂ := b6e21
             grind)
          | exact resolve b6e151 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e151
        have b6e155 : False := by grind
        exact b6e155
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
          have b7e63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          have b7e65 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e63
          have b7e66 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
          have b7e67 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
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
          have b7e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e559 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e560 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e559
          have b7e561 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e560
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e560
            | exact resolve b7e560 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e560
          have b7e563 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e561
               have r₂ := b7e93
               grind)
            | exact resolve b7e561 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e561
          have b7e565 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e563
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e563
            | exact resolve b7e563 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e563
          have b7e567 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e565
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e565
            | exact resolve b7e565 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e565
          have b7e570 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e567
               have i₂ := b7e128 x y
               grind)
            | exact superpose b7e128 b7e567
            | (have j1 := b7e128 x y
               grind)
            | exact resolve b7e567 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e572 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e567
               grind)
            | exact superpose b7e567 b7e14
            | exact resolve b7e14 b7e567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e567
          have b7e584 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e572
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e572
            | exact resolve b7e572 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e572
          have b7e586 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e570
               have r₂ := b7e93
               grind)
            | exact resolve b7e570 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e570
          have b7e589 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e586
               have r₂ := b7e22
               grind)
            | exact resolve b7e586 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e586
          have b7e590 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e589
               have i₂ := b7e584
               grind)
            | exact superpose b7e584 b7e589
            | exact resolve b7e589 b7e584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e584 b7e589
          have b7e591 : False := by grind
          exact b7e591
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
          have b8e115 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e783 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e115 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e784 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e783
               have r₂ := b8e23
               grind)
            | exact resolve b8e783 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e783
          have b8e786 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e784
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e784
            | exact resolve b8e784 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e784
          have b8e793 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e786
               grind)
            | exact superpose b8e786 b8e20
            | exact resolve b8e20 b8e786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e786
          have b8e853 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e793
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e793
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e793 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e793
          have b8e854 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e853
          have b8e856 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e854
               have r₂ := b8e21
               grind)
            | exact resolve b8e854 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e854
          have b8e859 : False := by grind
          exact b8e859

/-- `Equation1276`: `x = y ◇ (((x ◇ x) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation1276 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1276 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1276.models_iff G M).mp hM
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
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e17
        | exact resolve b0e17 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e46
        | exact resolve b0e46 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e46
      have b0e173 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e51 y
           grind)
        | exact superpose b0e51 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e51 y
           grind)
        | exact resolve b0e22 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e51
      have b0e187 : False := by grind
      exact b0e187
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
        have b1e48 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b1e49 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e49
        have b1e53 : (M.op x x) = (k x y) := by grind
        clear b1e48
        have b1e54 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e51 x
             grind)
          | exact superpose b1e51 b1e54
          | exact resolve b1e54 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e18
          | exact resolve b1e18 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e57 X0
             have i₂ := b1e51 X0
             grind)
          | exact superpose b1e51 b1e57
          | exact resolve b1e57 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e57
        have b1e70 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
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
        have b1e73 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e70
          | (have j0 := b1e70 X0
             grind)
          | exact resolve b1e70 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e126 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e23
          | exact resolve b1e23 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e582 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e73 (σ y)
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e73
          | (have j0 := b1e73 (σ y)
             grind)
          | (have r₁ := b1e73 (σ y)
             have r₂ := b1e55
             grind)
          | exact resolve b1e73 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e73
        have b1e588 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e582
        have b1e590 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e588
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e588
          | exact resolve b1e588 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e588
        have b1e592 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e590
             have r₂ := b1e126
             grind)
          | exact resolve b1e590 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e590
        have b1e593 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e592
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e592
          | exact resolve b1e592 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e592
        have b1e594 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e593
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e593
          | exact resolve b1e593 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e593
        have b1e595 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e594
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e594
          | exact resolve b1e594 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e594
        have b1e596 : False := by grind
        exact b1e596
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
        have b2e47 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : (M.op x x) = (k x y) := by grind
        clear b2e47
        have b2e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e48 (σ X0)
             grind)
          | exact superpose b2e48 b2e18
          | exact resolve b2e18 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e51 X0
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e51
          | exact resolve b2e51 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e51
        have b2e85 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e144 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e58 x
             grind)
          | exact superpose b2e58 b2e22
          | exact resolve b2e22 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e750 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e85 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e751 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e750
             have r₂ := b2e21
             grind)
          | exact resolve b2e750 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e750
        have b2e752 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e751
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e751
          | exact resolve b2e751 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e751
        have b2e753 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e752
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e752
          | exact resolve b2e752 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e752
        have b2e754 : False := by grind
        exact b2e754
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
        have b3e49 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e49
        have b3e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e51 (σ X0)
             grind)
          | exact superpose b3e51 b3e18
          | exact resolve b3e18 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e57 X0
             have i₂ := b3e51 X0
             grind)
          | exact superpose b3e51 b3e57
          | exact resolve b3e57 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e70 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e15
          | exact resolve b3e15 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e77 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e76
        have b3e78 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e77
          | exact resolve b3e77 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e79 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e51 x
             grind)
          | exact superpose b3e51 b3e78
          | exact resolve b3e78 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e78
        have b3e80 : (σ (M.op x y)) = (σ (k x y)) := by
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
        have b3e196 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e64 y
             grind)
          | exact superpose b3e64 b3e23
          | exact resolve b3e23 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e64
        have b3e213 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e70 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e214 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e213
             have r₂ := b3e20
             grind)
          | exact resolve b3e213 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e213
        have b3e218 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e214
             grind)
          | exact superpose b3e214 b3e80
          | exact resolve b3e80 b3e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e214
        have b3e222 : False := by grind
        exact b3e222
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
          have b4e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e64 (σ X0)
               grind)
            | exact superpose b4e64 b4e19
            | exact resolve b4e19 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e66 X0
               have i₂ := b4e64 X0
               grind)
            | exact superpose b4e64 b4e66
            | exact resolve b4e66 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64 b4e66
          have b4e149 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e75 x
               grind)
            | exact superpose b4e75 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e75 x
               grind)
            | exact resolve b4e28 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e75
          have b4e158 : False := by grind
          exact b4e158
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
          have b5e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e62 (σ X0)
               grind)
            | exact superpose b5e62 b5e19
            | exact resolve b5e19 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e64 X0
               have i₂ := b5e62 X0
               grind)
            | exact superpose b5e62 b5e64
            | exact resolve b5e64 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62 b5e64
          have b5e81 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e84 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e81
          have b5e85 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e84
               have r₂ := b5e25
               grind)
            | exact resolve b5e84 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e84
          have b5e99 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e138 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e73 y
               grind)
            | exact superpose b5e73 b5e23
            | exact resolve b5e23 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e747 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e99 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e748 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e747
               have r₂ := b5e24
               grind)
            | exact resolve b5e747 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e747
          have b5e750 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e748
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e748
            | exact resolve b5e748 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e748
          have b5e752 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e750
               have i₂ := b5e85
               grind)
            | exact superpose b5e85 b5e750
            | exact resolve b5e750 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85 b5e750
          have b5e753 : False := by grind
          exact b5e753
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
        have b6e47 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e47
        have b6e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e49
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e49
          | exact resolve b6e49 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e50
             grind)
          | exact superpose b6e50 b6e15
          | exact resolve b6e15 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e71 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e70
        have b6e72 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e71
          | exact resolve b6e71 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e73 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e72
          | exact resolve b6e72 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e72
        have b6e127 : (k x y) = (τ (σ (M.op x x))) := by
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
        have b6e128 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e127
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e127
          | exact resolve b6e127 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127
        have b6e151 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e128
             grind)
          | exact superpose b6e128 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e152 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e151
        have b6e154 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e152
             have r₂ := b6e21
             grind)
          | exact resolve b6e152 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e152
        have b6e156 : False := by grind
        exact b6e156
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
          have b7e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e62 (σ X0)
               grind)
            | exact superpose b7e62 b7e19
            | exact resolve b7e19 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e64 X0
               have i₂ := b7e62 X0
               grind)
            | exact superpose b7e62 b7e64
            | exact resolve b7e64 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e64
          have b7e82 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e84 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e82
          have b7e85 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e25
               grind)
            | exact resolve b7e84 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e84
          have b7e86 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e85
            | exact resolve b7e85 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e87 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e73 y
               grind)
            | exact superpose b7e73 b7e86
            | exact resolve b7e86 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e86
          have b7e92 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e87
               grind)
            | exact superpose b7e87 b7e14
            | exact resolve b7e14 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e93 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e92
            | exact resolve b7e92 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e149 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e150 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e149
          have b7e152 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e150
               have r₂ := b7e21
               grind)
            | exact resolve b7e150 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e154 : False := by grind
          exact b7e154
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
          have b8e105 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e798 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e105 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e799 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e798
               have r₂ := b8e24
               grind)
            | exact resolve b8e798 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e798
          have b8e801 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e799
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e799
            | exact resolve b8e799 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e799
          have b8e807 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e801
               grind)
            | exact superpose b8e801 b8e20
            | exact resolve b8e20 b8e801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e801
          have b8e830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e807
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e807
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e807 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e807
          have b8e831 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e830
          have b8e833 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e831
               have r₂ := b8e21
               grind)
            | exact resolve b8e831 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e836 : False := by grind
          exact b8e836

/-- `Equation1279`: `x = y ◇ (((x ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_pyx_pxy_Equation1279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x x) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e15
        | (have j0 := b0e15 X0 x
           grind)
        | (have r₁ := b0e15 X0 x
           have r₂ := b0e19
           grind)
        | exact resolve b0e15 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e15
        | (have j0 := b0e15 X0 (σ x)
           grind)
        | (have r₁ := b0e15 X0 (σ x)
           have r₂ := b0e20
           grind)
        | exact resolve b0e15 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b0e43 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e42 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e46 : ∀ X0 : G, (M.op (σ x) X0) = (k X0 (σ x)) := by
        intro X0
        first
        | (have j0 := b0e44 X0
           have j1 := b0e14 X0 (σ x)
           grind)
        | (have r₁ := b0e44 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e44 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e47 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
        intro X0
        first
        | (have j0 := b0e45 X0
           have j1 := b0e14 X0 x
           grind)
        | (have r₁ := b0e45 X0
           have r₂ := b0e14 X0 x
           grind)
        | exact resolve b0e45 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e80 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 x
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e17
        | exact resolve b0e17 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e82 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e80 X0
           have i₂ := b0e47 X0
           grind)
        | exact superpose b0e47 b0e80
        | exact resolve b0e80 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e80
      have b0e354 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e82 y
           grind)
        | exact superpose b0e82 b0e18
        | (have r₁ := b0e18
           have r₂ := b0e82 y
           grind)
        | exact resolve b0e18 b0e82
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e82
      have b0e365 : False := by grind
      exact b0e365
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e37 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e15 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) X0
             grind)
          | (have r₁ := b1e15 (σ y) x
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b1e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e40 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e16 X0 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 X0 x
             grind)
          | (have r₁ := b1e16 X0 x
             have r₂ := b1e20
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e40 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e45 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e43 X0
             have j1 := b1e15 X0 x
             grind)
          | (have r₁ := b1e43 X0
             have r₂ := b1e15 X0 x
             grind)
          | exact resolve b1e43 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e72 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e38 (σ X0)
             grind)
          | exact superpose b1e38 b1e18
          | exact resolve b1e18 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e102 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e72 x
             grind)
          | exact superpose b1e72 b1e19
          | exact resolve b1e19 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e111 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e102
             have i₂ := b1e45 y
             grind)
          | exact superpose b1e45 b1e102
          | exact resolve b1e102 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e102
        have b1e112 : False := by grind
        exact b1e112
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X2 X0
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X1
             have j1 := b2e17 X2 X2
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e50 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e256 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e60 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e257 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e256 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e256
        have b2e263 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e257 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e257 X0
             have r₂ := b2e15 X0 x
             grind)
          | exact resolve b2e257 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e257
        have b2e270 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e263 (σ X0)
             grind)
          | exact superpose b2e263 b2e18
          | exact resolve b2e18 b2e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e277 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e270 X0
             have i₂ := b2e263 X0
             grind)
          | exact superpose b2e263 b2e270
          | exact resolve b2e270 b2e263
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e263 b2e270
        have b2e513 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e277 x
             grind)
          | exact superpose b2e277 b2e21
          | exact resolve b2e21 b2e277
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e277
        have b2e533 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e513
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e513
          | exact resolve b2e513 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e513
        have b2e534 : False := by grind
        exact b2e534
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e37 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b3e38 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e37 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e68 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e38 (σ X0)
             grind)
          | exact superpose b3e38 b3e18
          | exact resolve b3e18 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e98 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e68 x
             grind)
          | exact superpose b3e68 b3e22
          | exact resolve b3e22 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e128 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e98
             grind)
          | exact superpose b3e98 b3e13
          | exact resolve b3e13 b3e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98
        have b3e130 : x = (k x x) := by
          first
          | (have i₁ := b3e128
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e128
          | exact resolve b3e128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e180 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e130
             grind)
          | exact superpose b3e130 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e181 : x = (M.op x x) := by grind
        clear b3e180
        have b3e185 : False := by grind
        exact b3e185
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e16 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e16 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | (have j0 := b4e16 (σ y) X0
               grind)
            | (have r₁ := b4e16 (σ y) x
               have r₂ := b4e24
               grind)
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b4e43 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e45 : ∀ X0 : G, (k y X0) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e42 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e81 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e44 (σ X0)
               grind)
            | exact superpose b4e44 b4e19
            | exact resolve b4e19 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e83 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e81 X0
               have i₂ := b4e45 X0
               grind)
            | exact superpose b4e45 b4e81
            | exact resolve b4e81 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e81
          have b4e178 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e83 x
               grind)
            | exact superpose b4e83 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e83 x
               grind)
            | exact resolve b4e20 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e186 : False := by grind
          exact b4e186
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e57 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X2 X0
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X1
               have j1 := b5e18 X2 X2
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e57 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e243 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e68 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68
          have b5e244 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e243 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e243
          have b5e250 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e244 X0
               have j1 := b5e16 X0 X0
               grind)
            | (have r₁ := b5e244 X0
               have r₂ := b5e16 X0 x
               grind)
            | exact resolve b5e244 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244
          have b5e256 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e250 (σ X0)
               grind)
            | exact superpose b5e250 b5e19
            | exact resolve b5e19 b5e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e261 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e256 X0
               have i₂ := b5e250 X0
               grind)
            | exact superpose b5e250 b5e256
            | exact resolve b5e256 b5e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250 b5e256
          have b5e564 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e261 y
               grind)
            | exact superpose b5e261 b5e24
            | exact resolve b5e24 b5e261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e261
          have b5e585 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e564
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e564
            | exact resolve b5e564 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e564
          have b5e586 : False := by grind
          exact b5e586
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e31 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = (M.op X0 (σ x)) := by
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
        have b6e32 : ∀ X0 : G, (k (σ x) X0) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b6e31 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e34 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e18 x X0
             have i₂ := b6e32 (σ X0)
             grind)
          | exact superpose b6e32 b6e18
          | exact resolve b6e18 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e49 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X2 X0
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X1
             have j1 := b6e17 X2 X2
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X0 X1
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e49 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e121 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e56 X0 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e122 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b6e121 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e121
        have b6e126 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e122 X0
             have j1 := b6e15 X0 X0
             grind)
          | (have r₁ := b6e122 X0
             have r₂ := b6e15 X0 x
             grind)
          | exact resolve b6e122 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e188 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e22
          | exact resolve b6e22 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e203 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e188
             have i₂ := b6e126 x
             grind)
          | exact superpose b6e126 b6e188
          | exact resolve b6e188 b6e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126 b6e188
        have b6e264 : (M.op x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e203
             grind)
          | exact superpose b6e203 b6e13
          | exact resolve b6e13 b6e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e203
        have b6e265 : x = (M.op x x) := by
          first
          | (have i₁ := b6e264
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e264
          | exact resolve b6e264 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e264
        have b6e270 : False := by grind
        exact b6e270
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e41 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) X0
               grind)
            | (have r₁ := b7e16 (σ y) x
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e41 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e44 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e19 y X0
               have i₂ := b7e42 (σ X0)
               grind)
            | exact superpose b7e42 b7e19
            | exact resolve b7e19 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e142 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e44 y
               grind)
            | exact superpose b7e44 b7e24
            | exact resolve b7e24 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e175 : (τ (σ y)) = (k y y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e142
               grind)
            | exact superpose b7e142 b7e14
            | exact resolve b7e14 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142
          have b7e177 : y = (k y y) := by
            first
            | (have i₁ := b7e175
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e175
            | exact resolve b7e175 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e175
          have b7e235 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e177
               grind)
            | exact superpose b7e177 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e177
          have b7e236 : y = (M.op y y) := by grind
          clear b7e235
          have b7e240 : False := by grind
          exact b7e240
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e72 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e72 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e105 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e78 (σ X0)
               grind)
            | exact superpose b8e78 b8e19
            | (have j1 := b8e78 (σ X0)
               grind)
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e3322 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e105 x
               grind)
            | exact superpose b8e105 b8e20
            | (have j1 := b8e105 x
               grind)
            | exact resolve b8e20 b8e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e3412 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e3322
               have r₂ := b8e23
               grind)
            | exact resolve b8e3322 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3322
          have b8e3449 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e3412
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e3412
            | (have j1 := b8e18 x x
               grind)
            | exact resolve b8e3412 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3412
          have b8e3459 : x = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e3449
          have b8e3463 : y = (M.op y y) := by
            first
            | (have r₁ := b8e3459
               have r₂ := b8e21
               grind)
            | exact resolve b8e3459 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3459
          have b8e3464 : False := by grind
          exact b8e3464

/-- `Equation1279`: `x = y ◇ (((x ◇ x) ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation1279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1279.models_iff G M).mp hM
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
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e17
        | exact resolve b0e17 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e46
        | exact resolve b0e46 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e46
      have b0e216 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e51 y
           grind)
        | exact superpose b0e51 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e51 y
           grind)
        | exact resolve b0e22 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e51
      have b0e229 : False := by grind
      exact b0e229
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
        have b1e48 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b1e49 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e49
        have b1e53 : (M.op x x) = (k x y) := by grind
        clear b1e48
        have b1e54 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e51 x
             grind)
          | exact superpose b1e51 b1e54
          | exact resolve b1e54 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e18
          | exact resolve b1e18 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e57 X0
             have i₂ := b1e51 X0
             grind)
          | exact superpose b1e51 b1e57
          | exact resolve b1e57 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e57
        have b1e70 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
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
        have b1e73 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e70 X0
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e70
          | (have j0 := b1e70 X0
             grind)
          | exact resolve b1e70 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e70
        have b1e126 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e23
          | exact resolve b1e23 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e530 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e73 (σ y)
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e73
          | (have j0 := b1e73 (σ y)
             grind)
          | (have r₁ := b1e73 (σ y)
             have r₂ := b1e55
             grind)
          | exact resolve b1e73 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e73
        have b1e535 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e530
        have b1e537 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e535
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e535
          | exact resolve b1e535 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e535
        have b1e539 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e537
             have r₂ := b1e126
             grind)
          | exact resolve b1e537 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e537
        have b1e540 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e539
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e539
          | exact resolve b1e539 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e539
        have b1e541 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e540
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e540
          | exact resolve b1e540 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e540
        have b1e542 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e541
             have i₂ := b1e64 y
             grind)
          | exact superpose b1e64 b1e541
          | exact resolve b1e541 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e541
        have b1e543 : False := by grind
        exact b1e543
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
        have b2e47 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
        have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : (M.op x x) = (k x y) := by grind
        clear b2e47
        have b2e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e48 (σ X0)
             grind)
          | exact superpose b2e48 b2e18
          | exact resolve b2e18 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e51 X0
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e51
          | exact resolve b2e51 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e51
        have b2e85 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e139 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e58 x
             grind)
          | exact superpose b2e58 b2e22
          | exact resolve b2e22 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e746 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e85 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e747 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e746
             have r₂ := b2e21
             grind)
          | exact resolve b2e746 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e746
        have b2e748 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e747
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e747
          | exact resolve b2e747 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e747
        have b2e749 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e748
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e748
          | exact resolve b2e748 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e748
        have b2e750 : False := by grind
        exact b2e750
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b3e21 : (M.op x y) = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e49 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e49
        have b3e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e70 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e15
          | exact resolve b3e15 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e77 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e76
        have b3e78 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e77
          | exact resolve b3e77 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e79 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e51 x
             grind)
          | exact superpose b3e51 b3e78
          | exact resolve b3e78 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e78
        have b3e80 : (σ (M.op x y)) = (σ (k x y)) := by
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
        have b3e133 : (k x y) = (τ (σ (M.op x y))) := by
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
        have b3e134 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b3e133
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e133
          | exact resolve b3e133 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e133
        have b3e173 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e70 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e174 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e173
             have r₂ := b3e20
             grind)
          | exact resolve b3e173 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e173
        have b3e177 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b3e134
             have i₂ := b3e174
             grind)
          | exact superpose b3e174 b3e134
          | exact resolve b3e134 b3e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134 b3e174
        have b3e182 : False := by grind
        exact b3e182
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
          have b4e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e64 (σ X0)
               grind)
            | exact superpose b4e64 b4e19
            | exact resolve b4e19 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e66 X0
               have i₂ := b4e64 X0
               grind)
            | exact superpose b4e64 b4e66
            | exact resolve b4e66 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64 b4e66
          have b4e149 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e75 x
               grind)
            | exact superpose b4e75 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e75 x
               grind)
            | exact resolve b4e28 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e75
          have b4e158 : False := by grind
          exact b4e158
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
          have b5e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e62 (σ X0)
               grind)
            | exact superpose b5e62 b5e19
            | exact resolve b5e19 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e64 X0
               have i₂ := b5e62 X0
               grind)
            | exact superpose b5e62 b5e64
            | exact resolve b5e64 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62 b5e64
          have b5e81 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e84 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e81
          have b5e85 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e84
               have r₂ := b5e25
               grind)
            | exact resolve b5e84 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e84
          have b5e99 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e138 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e73 y
               grind)
            | exact superpose b5e73 b5e23
            | exact resolve b5e23 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e745 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e99 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e99
          have b5e746 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e745
               have r₂ := b5e24
               grind)
            | exact resolve b5e745 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e745
          have b5e747 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e746
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e746
            | exact resolve b5e746 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e746
          have b5e748 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e747
               have i₂ := b5e85
               grind)
            | exact superpose b5e85 b5e747
            | exact resolve b5e747 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85 b5e747
          have b5e749 : False := by grind
          exact b5e749
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
        have b6e47 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e47
        have b6e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e49
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e49
          | exact resolve b6e49 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e50
             grind)
          | exact superpose b6e50 b6e15
          | exact resolve b6e15 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e71 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e70
        have b6e72 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e71
          | exact resolve b6e71 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e73 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e48 x
             grind)
          | exact superpose b6e48 b6e72
          | exact resolve b6e72 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e72
        have b6e127 : (k x y) = (τ (σ (M.op x x))) := by
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
        have b6e128 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e127
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e127
          | exact resolve b6e127 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e127
        have b6e148 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e128
             grind)
          | exact superpose b6e128 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e128
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e128
        have b6e149 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e148
        have b6e151 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e149
             have r₂ := b6e21
             grind)
          | exact resolve b6e149 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e153 : False := by grind
        exact b6e153
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
          have b7e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e62 (σ X0)
               grind)
            | exact superpose b7e62 b7e19
            | exact resolve b7e19 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e64 X0
               have i₂ := b7e62 X0
               grind)
            | exact superpose b7e62 b7e64
            | exact resolve b7e64 b7e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e64
          have b7e82 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e84 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e82
          have b7e85 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e84
               have r₂ := b7e25
               grind)
            | exact resolve b7e84 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e84
          have b7e86 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e85
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e85
            | exact resolve b7e85 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e87 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e73 y
               grind)
            | exact superpose b7e73 b7e86
            | exact resolve b7e86 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e86
          have b7e92 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e87
               grind)
            | exact superpose b7e87 b7e14
            | exact resolve b7e14 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e93 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e92
            | exact resolve b7e92 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e149 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e150 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e149
          have b7e152 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e150
               have r₂ := b7e21
               grind)
            | exact resolve b7e150 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e154 : False := by grind
          exact b7e154
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
          have b8e105 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e796 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e105 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e797 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e796
               have r₂ := b8e24
               grind)
            | exact resolve b8e796 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e796
          have b8e798 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e797
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e797
            | exact resolve b8e797 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e797
          have b8e802 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e798
               grind)
            | exact superpose b8e798 b8e20
            | exact resolve b8e20 b8e798
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e798
          have b8e825 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e802
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e802
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e802 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e802
          have b8e826 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e825
          have b8e828 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e826
               have r₂ := b8e21
               grind)
            | exact resolve b8e826 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e826
          have b8e831 : False := by grind
          exact b8e831

/-- `Equation1286`: `x = y ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation1286 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1286 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1286.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
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
      have b0e57 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e59 : False := by grind
      exact b0e59
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
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e148 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e49 x y
               grind)
            | exact superpose b4e49 b4e20
            | (have j1 := b4e49 x y
               grind)
            | exact resolve b4e20 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e156 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e148
               have r₂ := b4e23
               grind)
            | exact resolve b4e148 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e379 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e156
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e156
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e156
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e156
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e156 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e380 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e379
          have b4e381 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e380
               have r₂ := b4e21
               grind)
            | exact resolve b4e380 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e380
          have b4e383 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e381
               grind)
            | exact superpose b4e381 b4e20
            | exact resolve b4e20 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e385 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e381
               grind)
            | exact superpose b4e381 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e381
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e381
               grind)
            | exact resolve b4e17 b4e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e381
          have b4e387 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e385
          have b4e389 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e387
               have r₂ := b4e23
               grind)
            | exact resolve b4e387 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e387
          have b4e392 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e389
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e389
            | exact resolve b4e389 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e389
          have b4e457 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e392
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e392
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e392 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e392
          have b4e477 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e457
          have b4e493 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e477
               have r₂ := b4e383
               grind)
            | exact resolve b4e477 b4e383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e383 b4e477
          have b4e494 : x = (M.op x y) := by
            first
            | (have r₁ := b4e493
               have r₂ := b4e21
               grind)
            | exact resolve b4e493 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e493
          have b4e534 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e494
               grind)
            | exact superpose b4e494 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e494
               grind)
            | exact resolve b4e17 b4e494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e536 : x = y ∨ x = (k y x) := by grind
          clear b4e534
          have b4e537 : x = (k y x) := by
            first
            | (have r₁ := b4e536
               have r₂ := b4e21
               grind)
            | exact resolve b4e536 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e536
          have b4e571 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e156
               have i₂ := b4e537
               grind)
            | exact superpose b4e537 b4e156
            | exact resolve b4e156 b4e537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156 b4e537
          have b4e575 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e571
               have i₂ := b4e494
               grind)
            | exact superpose b4e494 b4e571
            | exact resolve b4e571 b4e494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e571
          have b4e576 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e575
          have b4e606 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e576
               grind)
            | exact superpose b4e576 b4e20
            | exact resolve b4e20 b4e576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e576
          have b4e614 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e606
               have i₂ := b4e494
               grind)
            | exact superpose b4e494 b4e606
            | exact resolve b4e606 b4e494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e494 b4e606
          have b4e615 : False := by grind
          exact b4e615
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e36 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e39 : x = y ∨ y = (k x y) := by grind
          clear b5e36
          have b5e40 : y = (k x y) := by
            first
            | (have r₁ := b5e39
               have r₂ := b5e21
               grind)
            | exact resolve b5e39 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e43 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e119 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e625 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e119 y x
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e119
            | (have j0 := b5e119 y x
               grind)
            | exact resolve b5e119 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e119
          have b5e632 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e625
          have b5e636 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e632
               have r₂ := b5e24
               grind)
            | exact resolve b5e632 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e632
          have b5e640 : False := by grind
          exact b5e640
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e42 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ y) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e46
               grind)
            | exact superpose b7e46 b7e14
            | exact resolve b7e14 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : y = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : y = (M.op y x) ∨ x = y := by grind
          clear b7e60
          have b7e63 : x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e65 : False := by grind
          exact b7e65
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e101 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e108 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e101
               have r₂ := b8e23
               grind)
            | exact resolve b8e101 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
          have b8e346 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e108
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e108
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e108
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e108
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e108 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e347 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e346
          have b8e348 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e347
               have r₂ := b8e21
               grind)
            | exact resolve b8e347 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e347
          have b8e350 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e348
               grind)
            | exact superpose b8e348 b8e20
            | exact resolve b8e20 b8e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e352 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e348
               grind)
            | exact superpose b8e348 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e348
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e348
               grind)
            | exact resolve b8e17 b8e348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e348
          have b8e354 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e352
          have b8e356 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e354
               have r₂ := b8e23
               grind)
            | exact resolve b8e354 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e354
          have b8e359 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e356
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e356
            | exact resolve b8e356 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e356
          have b8e424 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e359
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e359
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e359 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e359
          have b8e444 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e424
          have b8e460 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e444
               have r₂ := b8e350
               grind)
            | exact resolve b8e444 b8e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e350 b8e444
          have b8e461 : x = (M.op x y) := by
            first
            | (have r₁ := b8e460
               have r₂ := b8e21
               grind)
            | exact resolve b8e460 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e501 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e461
               grind)
            | exact superpose b8e461 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e461
               grind)
            | exact resolve b8e17 b8e461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e503 : x = y ∨ x = (k y x) := by grind
          clear b8e501
          have b8e504 : x = (k y x) := by
            first
            | (have r₁ := b8e503
               have r₂ := b8e21
               grind)
            | exact resolve b8e503 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e503
          have b8e538 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e108
               have i₂ := b8e504
               grind)
            | exact superpose b8e504 b8e108
            | exact resolve b8e108 b8e504
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108 b8e504
          have b8e542 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e538
               have i₂ := b8e461
               grind)
            | exact superpose b8e461 b8e538
            | exact resolve b8e538 b8e461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e538
          have b8e543 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e542
          have b8e571 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e543
               grind)
            | exact superpose b8e543 b8e20
            | exact resolve b8e20 b8e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e543
          have b8e579 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e571
               have i₂ := b8e461
               grind)
            | exact superpose b8e461 b8e571
            | exact resolve b8e571 b8e461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e461 b8e571
          have b8e580 : False := by grind
          exact b8e580

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation1483 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e59 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e62 : False := by grind
      exact b0e62
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x y) (M.op y x) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : x ≠ y := by grind
        have b3e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
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
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e25
          | exact resolve b3e25 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : (M.op x y) = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e64 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e65 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e67 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b4e65
          have b4e68 : x = y ∨ (M.op x y) = (k y x) := by grind
          clear b4e64
          have b4e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b4e67
               have r₂ := b4e23
               grind)
            | exact resolve b4e67 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e72 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e68
               have r₂ := b4e21
               grind)
            | exact resolve b4e68 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e75 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e71
            | exact resolve b4e71 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e77 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e72
               grind)
            | exact superpose b4e72 b4e75
            | exact resolve b4e75 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e75
          have b4e79 : False := by grind
          exact b4e79
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x y) = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e61 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e17 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e22
               grind)
            | (have r₁ := b5e17 x y
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : x = y ∨ (M.op x y) = (k y x) := by grind
          clear b5e61
          have b5e65 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e69 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e238 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e69 x y
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e69 y x
               grind)
            | exact superpose b5e69 b5e24
            | (have j1 := b5e69 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e69 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e69 x y
               grind)
            | exact resolve b5e24 b5e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e268 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b5e238
          have b5e275 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b5e268
               have r₂ := b5e23
               grind)
            | exact resolve b5e268 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e268
          have b5e282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e275
               have i₂ := b5e65
               grind)
            | exact superpose b5e65 b5e275
            | exact resolve b5e275 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e275
          have b5e285 : False := by grind
          exact b5e285
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
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x y) ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e61 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e17
            | (have j0 := b7e17 (σ x) (σ y)
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | (have r₁ := b7e17 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e63 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b7e61
          have b7e65 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e20
            | exact resolve b7e20 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e76 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e69
            | (have j1 := b7e18 y x
               grind)
            | (have r₁ := b7e69
               have r₂ := b7e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b7e69
               have r₂ := b7e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b7e69 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e77 : (M.op x y) = (M.op y x) ∨ x = y := by grind
          clear b7e76
          have b7e78 : x = y := by
            first
            | (have r₁ := b7e77
               have r₂ := b7e22
               grind)
            | exact resolve b7e77 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e79 : False := by grind
          exact b7e79
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x y) ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e74 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e193 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e74 x y
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e74 y x
               grind)
            | exact superpose b8e74 b8e24
            | (have j1 := b8e74 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e74 y x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e74 x y
               grind)
            | exact resolve b8e24 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e223 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b8e193
          have b8e230 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e223
               have r₂ := b8e23
               grind)
            | exact resolve b8e223 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e223
          have b8e256 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e230
               grind)
            | exact superpose b8e230 b8e20
            | exact resolve b8e20 b8e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e230
          have b8e289 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e256
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e256
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e256
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e256
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e256 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256
          have b8e290 : (M.op x y) = (M.op y x) ∨ x = y := by grind
          clear b8e289
          have b8e291 : x = y := by
            first
            | (have r₁ := b8e290
               have r₂ := b8e22
               grind)
            | exact resolve b8e290 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e290
          have b8e292 : False := by grind
          exact b8e292
