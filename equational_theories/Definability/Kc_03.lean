import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_y_x_pyx_pxy_Equation3587 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3587 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e32 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
      have b0e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
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
      have b0e39 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e33
        | exact resolve b0e33 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e40 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e53 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e39 (σ x)
           grind)
        | exact superpose b0e39 b0e18
        | exact resolve b0e18 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e55 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e53
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e53
        | exact resolve b0e53 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e53
      have b0e56 : False := by grind
      exact b0e56
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e36 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b1e12 y x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
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
        have b1e43 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e37
          | exact resolve b1e37 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e44 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e36
          | exact resolve b1e36 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e59 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e43 (σ x)
             grind)
          | exact superpose b1e43 b1e19
          | exact resolve b1e19 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e61 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e59
          | exact resolve b1e59 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44 b1e59
        have b1e62 : False := by grind
        exact b1e62
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
        have b2e33 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b2e27 X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e35 : ∀ X0 : G, y ≠ X0 ∨ y = (k y X0) := by
          intro X0
          first
          | (have i₁ := b2e15 y X0
             have i₂ := b2e33 X0
             grind)
          | exact superpose b2e33 b2e15
          | (have j0 := b2e15 y X0
             grind)
          | (have r₁ := b2e15 y y
             have r₂ := b2e33 y
             grind)
          | exact resolve b2e15 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e42 : y = (k y y) := by
          first
          | (have j0 := b2e35 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e364 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47
        have b2e365 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e364 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e364
        have b2e879 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e365 y
             have i₂ := b2e42
             grind)
          | exact superpose b2e42 b2e365
          | (have j0 := b2e365 y
             grind)
          | exact resolve b2e365 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e365
        have b2e882 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e879
        have b2e888 : False := by grind
        exact b2e888
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
          intro X0 X1 X2
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e36 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
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
        have b3e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e37 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e37
          | exact resolve b3e37 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e44 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e36 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e36
          | exact resolve b3e36 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e59 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e43 (σ x)
             grind)
          | exact superpose b3e43 b3e19
          | exact resolve b3e19 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e61 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e44 x
             grind)
          | exact superpose b3e44 b3e59
          | exact resolve b3e59 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e59
        have b3e62 : False := by grind
        exact b3e62
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, y = (M.op X0 (M.op y y)) := by
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
          have b4e37 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ y))) := by
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
          have b4e43 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e44 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e36
            | exact resolve b4e36 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e61 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e43 (σ x)
               grind)
            | exact superpose b4e43 b4e20
            | exact resolve b4e20 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e63 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e61
               have i₂ := b4e44 x
               grind)
            | exact superpose b4e44 b4e61
            | exact resolve b4e61 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e61
          have b4e64 : False := by grind
          exact b4e64
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : y ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y y
               grind)
            | (have r₁ := b5e16 y y
               have r₂ := b5e22
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e26 : y = (k y y) := by grind
          clear b5e25
          have b5e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e313 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e54 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e314 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e313 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e313
          have b5e879 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e314 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e314
            | (have j0 := b5e314 y
               grind)
            | exact resolve b5e314 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e314
          have b5e882 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e879
          have b5e888 : False := by grind
          exact b5e888
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
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e21 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e38 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
        have b6e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e40 X0 X1 x X3
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e44 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e38 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e38
          | exact resolve b6e38 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e38
        have b6e88 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e42 (M.op X0 X1) X1 x
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e365 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 (M.op X0 X1)
             have i₂ := b6e88 X0 X1
             grind)
          | exact superpose b6e88 b6e15
          | (have j0 := b6e15 X1 (M.op X0 X1)
             grind)
          | (have r₁ := b6e15 X1 (M.op X0 X1)
             have r₂ := b6e88 X0 X1
             grind)
          | exact resolve b6e15 b6e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e374 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e365 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e365
        have b6e398 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e374 x (σ y)
             have i₂ := b6e44 x
             grind)
          | exact superpose b6e44 b6e374
          | exact resolve b6e374 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e374
        have b6e418 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e398
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e398
          | exact resolve b6e398 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e398
        have b6e449 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e418
             grind)
          | exact superpose b6e418 b6e13
          | exact resolve b6e13 b6e418
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e418
        have b6e466 : y = (k y y) := by
          first
          | (have i₁ := b6e449
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e449
          | exact resolve b6e449 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e449
        have b6e478 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e466
             grind)
          | exact superpose b6e466 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e466
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e466
        have b6e479 : y = (M.op y y) := by grind
        clear b6e478
        have b6e486 : False := by grind
        exact b6e486
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ y) (σ y)
               grind)
            | (have r₁ := b7e16 (σ y) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b7e25
          have b7e27 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : y = (k y y) := by
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
          have b7e58 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e67 : y = (M.op y y) := by grind
          clear b7e58
          have b7e72 : False := by grind
          exact b7e72
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b8e310 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e58 x y
               grind)
            | exact superpose b8e58 b8e20
            | (have j1 := b8e58 y y
               grind)
            | exact resolve b8e20 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e367 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b8e310
               have r₂ := b8e24
               grind)
            | exact resolve b8e310 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e310
          have b8e374 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e367
               have r₂ := b8e23
               grind)
            | exact resolve b8e367 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e378 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e374
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e374
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e374 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e374
          have b8e379 : y = (M.op y y) ∨ y = (M.op y x) := by grind
          clear b8e378
          have b8e382 : y = (M.op y x) := by
            first
            | (have r₁ := b8e379
               have r₂ := b8e22
               grind)
            | exact resolve b8e379 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e379
          have b8e386 : False := by grind
          exact b8e386

/-- `Equation3587`: `x ◇ y = z ◇ ((x ◇ y) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation3587 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3587 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3587.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
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
      have b0e82 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e86 : False := by grind
      exact b0e86
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e34 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e27
          have b5e38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e34
            | exact resolve b5e34 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e39 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e38
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b5e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e42 X0 X1 x X3
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e42
            | exact resolve b5e42 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e50 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e53 : x = y ∨ y = (k x y) := by grind
          clear b5e50
          have b5e54 : y = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e134 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e43 (σ X0) (σ X1) x
               have i₂ := b5e57 X0 X1
               grind)
            | exact superpose b5e57 b5e43
            | (have j1 := b5e57 X1 X0
               grind)
            | exact resolve b5e43 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e157 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14 (M.op (τ X0) (τ X0))
               have i₂ := b5e39 X0
               grind)
            | exact superpose b5e39 b5e14
            | exact resolve b5e14 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e382 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e43 (τ X0) (τ X0) x
               have i₂ := b5e157 X0
               grind)
            | exact superpose b5e157 b5e43
            | exact resolve b5e43 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157
          have b5e501 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e382 (M.op X0 X1) X1
               have i₂ := b5e43 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b5e43 b5e382
            | exact resolve b5e382 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e382
          have b5e960 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e134 x y x
               have i₂ := b5e54
               grind)
            | exact superpose b5e54 b5e134
            | (have j0 := b5e134 x y x
               grind)
            | exact resolve b5e134 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e134
          have b5e994 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e960 X0
               grind)
            | (have r₁ := b5e960 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e960 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e960
          have b5e999 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e994 X0
               grind)
            | (have r₁ := b5e994 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e994 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e994
          have b5e1018 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) := by
            intro X1
            first
            | (have i₁ := b5e501 x (σ y) x
               have i₂ := b5e999 x
               grind)
            | exact superpose b5e999 b5e501
            | exact resolve b5e501 b5e999
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e501 b5e999
          have b5e1031 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b5e1018 X1
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e1018
            | exact resolve b5e1018 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1018
          have b5e1084 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e1031 x
               grind)
            | exact superpose b5e1031 b5e22
            | exact resolve b5e22 b5e1031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1031
          have b5e1085 : False := by grind
          exact b5e1085
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e33 : ∀ X0 : G, (σ x) = (M.op X0 (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X0 X1) X1) X3
               have i₂ := b7e13 X0 X1 (M.op X2 (M.op (M.op X0 X1) X1))
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b7e35 X0 X1 x X3
               have i₂ := b7e13 X0 X1 x
               grind)
            | exact superpose b7e13 b7e35
            | exact resolve b7e35 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e38 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e33 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e46 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
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
          have b7e61 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e52
               grind)
            | exact superpose b7e52 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e62 : y = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : y = (M.op y x) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e118 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e38 (σ x)
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e38
            | exact resolve b7e38 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e38
          have b7e191 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e118
               grind)
            | exact superpose b7e118 b7e14
            | exact resolve b7e14 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e208 : x = (M.op x x) := by
            first
            | (have i₁ := b7e191
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e191
            | exact resolve b7e191 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e191
          have b7e228 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e36 x x x
               have i₂ := b7e208
               grind)
            | exact superpose b7e208 b7e36
            | exact resolve b7e36 b7e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e208
          have b7e267 : x = y := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e228 y
               grind)
            | exact superpose b7e228 b7e64
            | exact resolve b7e64 b7e228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e228
          have b7e268 : False := by grind
          exact b7e268
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b8e34 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e33 X0 X1 x X3
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e62 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e26
          have b8e67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e62 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e62
            | exact resolve b8e62 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e67
          have b8e85 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 (σ X0) (σ X0) x
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e34
            | exact resolve b8e34 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e108 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X1) (σ X0) x
               have i₂ := b8e60 X0 X1
               grind)
            | exact superpose b8e60 b8e34
            | (have j1 := b8e60 X1 X0
               grind)
            | exact resolve b8e34 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e139 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e68 X0
               grind)
            | exact superpose b8e68 b8e14
            | exact resolve b8e14 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e181 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e85 (M.op X0 X1) X1
               have i₂ := b8e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b8e34 b8e85
            | exact resolve b8e85 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e247 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 (τ X0) (τ X0) x
               have i₂ := b8e139 X0
               grind)
            | exact superpose b8e139 b8e34
            | exact resolve b8e34 b8e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e341 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e247 (M.op X0 X1) X1
               have i₂ := b8e34 X0 X1 (M.op X0 X1)
               grind)
            | exact superpose b8e34 b8e247
            | exact resolve b8e247 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e247
          have b8e829 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e20
               have i₂ := b8e108 y x X0
               grind)
            | exact superpose b8e108 b8e20
            | (have j1 := b8e108 y x X0
               grind)
            | exact resolve b8e20 b8e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e878 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e829 X0
               grind)
            | (have r₁ := b8e829 X0
               have r₂ := b8e23
               grind)
            | exact resolve b8e829 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e829
          have b8e2811 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ x = y := by
            intro X0
            first
            | (have i₁ := b8e878 X0
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e878
            | (have j0 := b8e878 X0
               have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e878 X0
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e878 X0
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e878 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e878
          have b8e2812 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ x = y := by
            intro X0
            first
            | (have j0 := b8e2811 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2811
          have b8e2813 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e2812 X0
               grind)
            | (have r₁ := b8e2812 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e2812 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2812
          have b8e2838 : ∀ X1 : G, (τ (σ y)) = (M.op X1 (τ (σ y))) ∨ y = (M.op y x) := by
            intro X1
            first
            | (have i₁ := b8e341 x (σ y) x
               have i₂ := b8e2813 x
               grind)
            | exact superpose b8e2813 b8e341
            | exact resolve b8e341 b8e2813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e341 b8e2813
          have b8e2864 : ∀ X1 : G, y = (M.op X1 y) ∨ y = (M.op y x) := by
            intro X1
            first
            | (have i₁ := b8e2838 X1
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e2838
            | exact resolve b8e2838 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2838
          have b8e2895 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ y = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b8e34 y x x
               have i₂ := b8e2864 X1
               grind)
            | exact superpose b8e2864 b8e34
            | (have j1 := b8e2864 X0
               grind)
            | exact resolve b8e34 b8e2864
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e2864
          have b8e2949 : ∀ X0 : G, y ≠ y ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e2895 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2895
          have b8e2950 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b8e2949 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2949
          have b8e3103 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e181 x y x
               have i₂ := b8e2950 x
               grind)
            | exact superpose b8e2950 b8e181
            | exact resolve b8e181 b8e2950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181
          have b8e3324 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3103 (σ x)
               grind)
            | exact superpose b8e3103 b8e20
            | exact resolve b8e20 b8e3103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3103
          have b8e3345 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e3324
               have i₂ := b8e2950 x
               grind)
            | exact superpose b8e2950 b8e3324
            | exact resolve b8e3324 b8e2950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2950 b8e3324
          have b8e3346 : False := by grind
          exact b8e3346

/-- `Equation3600`: `x ◇ y = z ◇ ((y ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_y_x_pyx_Equation3600 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3600 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3600.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
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
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y x) := by grind
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
        have b0e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X1 (τ X0)
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
        have b0e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
        have b0e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b0e38 X0 X1 x X3
             have i₂ := b0e12 X0 X1 x
             grind)
          | exact superpose b0e12 b0e38
          | exact resolve b0e38 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38
        have b0e41 : ∀ X0 : G, y = (M.op X0 y) := by
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
        have b0e46 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e15 y X0
             have i₂ := b0e41 X0
             grind)
          | exact superpose b0e41 b0e15
          | (have j0 := b0e15 y X0
             grind)
          | (have r₁ := b0e15 y X0
             have r₂ := b0e41 X0
             grind)
          | exact resolve b0e15 b0e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e48 : ∀ X0 : G, (k y X0) = X0 := by
          intro X0
          first
          | (have j0 := b0e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e46
        have b0e82 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X1 X0 x
             have i₂ := b0e40 (M.op X0 X1) X0 x
             grind)
          | exact superpose b0e40 b0e12
          | exact resolve b0e12 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e110 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b0e33 X0 y
             have i₂ := b0e48 (τ X0)
             grind)
          | exact superpose b0e48 b0e33
          | exact resolve b0e33 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e48
        have b0e118 : ∀ X0 : G, (k (σ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b0e110 X0
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e110
          | exact resolve b0e110 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e110
        have b0e124 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
        clear b0e118
        have b0e128 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e124
             have i₂ := b0e82 (σ y) (σ y)
             grind)
          | exact superpose b0e82 b0e124
          | exact resolve b0e124 b0e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e82 b0e124
        have b0e129 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b0e128
        have b0e573 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e40 (σ y) (σ y) x
             have i₂ := b0e129
             grind)
          | exact superpose b0e129 b0e40
          | exact resolve b0e40 b0e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40 b0e129
        have b0e662 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e573 (σ x)
             grind)
          | exact superpose b0e573 b0e24
          | (have r₁ := b0e24
             have r₂ := b0e573 (σ x)
             grind)
          | exact resolve b0e24 b0e573
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e573
        have b0e664 : False := by grind
        exact b0e664
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b1e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b1e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b1e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : x = (M.op y x) := by grind
          have b1e23 : y ≠ (M.op x y) := by grind
          have b1e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 (τ X0) X1
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e19
            | exact resolve b1e19 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b1e34 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
          have b1e35 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
          have b1e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b1e40 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b1e38 X0 X1 x X3
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e38
            | exact resolve b1e38 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38
          have b1e41 : x = (M.op x y) := by
            first
            | (have i₁ := b1e34 x
               have i₂ := b1e35 x
               grind)
            | exact superpose b1e35 b1e34
            | exact resolve b1e34 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e34 b1e35
          have b1e42 : x ≠ y := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e41
               grind)
            | exact superpose b1e41 b1e23
            | exact resolve b1e23 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e48 : y = (k y x) ∨ y = (M.op x y) := by grind
          have b1e49 : y = (k y x) := by
            first
            | (have r₁ := b1e48
               have r₂ := b1e23
               grind)
            | exact resolve b1e48 b1e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e48
          have b1e53 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X2 X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e18 X1 X2
               have i₂ := b1e18 X1 X0
               grind)
            | (have i₁ := b1e18 X0 X1
               have i₂ := b1e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b1e18 b1e18
            | (have j0 := b1e18 X1 X2
               have j1 := b1e18 X1 X2
               grind)
            | exact resolve b1e18 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b1e19 X1 X0
               have i₂ := b1e18 (σ X1) (σ X0)
               grind)
            | exact superpose b1e18 b1e19
            | (have j1 := b1e18 (σ X1) (σ X0)
               grind)
            | exact resolve b1e19 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e94 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X0 x
               have i₂ := b1e40 (M.op X0 X1) X0 x
               grind)
            | exact superpose b1e40 b1e13
            | exact resolve b1e13 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e97 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e16 (M.op X0 X1) X2
               have i₂ := b1e40 X0 X1 X2
               grind)
            | exact superpose b1e40 b1e16
            | (have j0 := b1e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b1e16 (M.op X0 X1) x
               have r₂ := b1e40 X0 X1 x
               grind)
            | exact resolve b1e16 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e101 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b1e97 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e97
          have b1e111 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b1e115 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e14 (k (τ X0) X1)
               have i₂ := b1e32 X0 X1
               grind)
            | exact superpose b1e32 b1e14
            | exact resolve b1e14 b1e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e32
          have b1e116 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e111 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e111
            | (have j0 := b1e111 X0
               grind)
            | exact resolve b1e111 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e111
          have b1e117 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e116 X0
               have i₂ := b1e94 (τ X0) (τ X0)
               grind)
            | exact superpose b1e94 b1e116
            | (have j0 := b1e116 X0
               grind)
            | exact resolve b1e116 b1e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e116
          have b1e123 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e33 X0 X1
               have i₂ := b1e18 X1 (τ X0)
               grind)
            | exact superpose b1e18 b1e33
            | (have j1 := b1e18 X1 (τ X0)
               grind)
            | exact resolve b1e33 b1e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e530 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b1e54 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e54
          have b1e659 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b1e49
               have i₂ := b1e53 x y X0
               grind)
            | exact superpose b1e53 b1e49
            | (have j1 := b1e53 X0 y X0
               grind)
            | exact resolve b1e49 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e53
          have b1e664 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b1e659 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e659
          have b1e672 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ x = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b1e664 X0
               grind)
            | (have r₁ := b1e664 X0
               have r₂ := b1e23
               grind)
            | (have r₁ := b1e664 x
               have r₂ := b1e23
               grind)
            | exact resolve b1e664 b1e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e664
          have b1e719 : ∀ X0 X1 X2 : G, (k (τ X2) (k X0 (τ X1))) = (τ (k X2 (k (σ X0) X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e115 X2 (k X0 (τ X1))
               have i₂ := b1e33 X1 X0
               grind)
            | exact superpose b1e33 b1e115
            | exact resolve b1e115 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e33
          have b1e726 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e115 (M.op X1 X2) X0
               have i₂ := b1e101 X1 X2 (σ X0)
               grind)
            | exact superpose b1e101 b1e115
            | exact resolve b1e115 b1e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e101 b1e115
          have b1e744 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e726 X0 X1 X2
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e726
            | exact resolve b1e726 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e726
          have b1e1801 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e117 X0
               have i₂ := b1e123 X0 (τ X0)
               grind)
            | exact superpose b1e123 b1e117
            | (have j0 := b1e117 X0
               have j1 := b1e123 X0 (τ X0)
               grind)
            | exact resolve b1e117 b1e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e117 b1e123
          have b1e1867 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b1e1801 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1801
          have b1e1893 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b1e1867 X0
               have i₂ := b1e15 X0
               grind)
            | exact superpose b1e15 b1e1867
            | (have j0 := b1e1867 X0
               grind)
            | exact resolve b1e1867 b1e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e1867
          have b1e2398 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e530 x y
               have i₂ := b1e49
               grind)
            | exact superpose b1e49 b1e530
            | (have j0 := b1e530 x y
               grind)
            | exact resolve b1e530 b1e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49 b1e530
          have b1e2403 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b1e2398
          have b1e17808 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ X0)) (k X0 (τ (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e719 X0 (σ X0) (σ X0)
               have i₂ := b1e1893 (σ X0)
               grind)
            | exact superpose b1e1893 b1e719
            | (have j1 := b1e1893 (σ X0)
               grind)
            | exact resolve b1e719 b1e1893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e719 b1e1893
          have b1e17921 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
            intro X0
            first
            | (have i₁ := b1e17808 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e17808
            | (have j0 := b1e17808 X0
               grind)
            | exact resolve b1e17808 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e17808
          have b1e17952 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e17921 X0
               have i₂ := b1e14 X0
               grind)
            | exact superpose b1e14 b1e17921
            | (have j0 := b1e17921 X0
               grind)
            | exact resolve b1e17921 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e17921
          have b1e18158 : y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op (k y y) y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b1e672 (k y y)
               have i₂ := b1e17952 y
               grind)
            | exact superpose b1e17952 b1e672
            | (have j0 := b1e672 (k y y)
               have j1 := b1e17952 y
               grind)
            | exact resolve b1e672 b1e17952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e672 b1e17952
          have b1e18159 : y = (M.op (k y y) y) ∨ x = (k y y) ∨ y = (M.op y y) := by grind
          clear b1e18158
          have b1e18197 : x = y ∨ y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have i₁ := b1e18159
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e18159
            | exact resolve b1e18159 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e18159
          have b1e18232 : y = (M.op (k y y) y) ∨ x = (k y y) := by
            first
            | (have r₁ := b1e18197
               have r₂ := b1e42
               grind)
            | exact resolve b1e18197 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e18197
          have b1e18331 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e94 (σ y) (σ y)
               have i₂ := b1e2403
               grind)
            | exact superpose b1e2403 b1e94
            | exact resolve b1e94 b1e2403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e94 b1e2403
          have b1e18399 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (k y y) := by
            intro X0
            first
            | (have i₁ := b1e40 (k y y) y x
               have i₂ := b1e18232
               grind)
            | exact superpose b1e18232 b1e40
            | exact resolve b1e40 b1e18232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40 b1e18232
          have b1e18758 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) ∨ x = (k y y) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 y X1
               have i₂ := b1e18399 (M.op y X0)
               grind)
            | exact superpose b1e18399 b1e13
            | exact resolve b1e13 b1e18399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e23888 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ x = (k y y) := by
            intro X0
            first
            | (have i₁ := b1e23
               have i₂ := b1e18758 x X0
               grind)
            | (have i₁ := b1e23
               have i₂ := b1e18758 X0 x
               grind)
            | exact superpose b1e18758 b1e23
            | exact resolve b1e23 b1e18758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e18758
          have b1e23945 : x = (k y y) := by
            first
            | (have r₁ := b1e23888 x
               have r₂ := b1e18399 x
               grind)
            | exact resolve b1e23888 b1e18399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e18399 b1e23888
          have b1e54285 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e744 X0 (σ x) (σ y)
               have i₂ := b1e18331
               grind)
            | exact superpose b1e18331 b1e744
            | exact resolve b1e744 b1e18331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e744 b1e18331
          have b1e54323 : ∀ X0 : G, (k y X0) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e54285 X0
               have i₂ := b1e14 y
               grind)
            | exact superpose b1e14 b1e54285
            | exact resolve b1e54285 b1e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e54285
          have b1e55715 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e20
               have i₂ := b1e54323 X0
               grind)
            | exact superpose b1e54323 b1e20
            | (have j1 := b1e54323 X0
               grind)
            | exact resolve b1e20 b1e54323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e54323
          have b1e55809 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b1e55715 X0
               have i₂ := b1e41
               grind)
            | exact superpose b1e41 b1e55715
            | (have j0 := b1e55715 X0
               grind)
            | exact resolve b1e55715 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41 b1e55715
          have b1e55810 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b1e55809 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e55809
          have b1e56204 : x = y := by
            first
            | (have i₁ := b1e23945
               have i₂ := b1e55810 y
               grind)
            | exact superpose b1e55810 b1e23945
            | exact resolve b1e23945 b1e55810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e23945 b1e55810
          have b1e56361 : False := by grind
          exact b1e56361
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e23 : y ≠ (M.op x y) := by grind
          have b2e24 : x ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b2e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e31 X0 X1
               grind)
            | exact superpose b2e31 b2e14
            | exact resolve b2e14 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31
          have b2e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b2e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b2e40 X0 X1 x X3
               have i₂ := b2e13 X0 X1 x
               grind)
            | exact superpose b2e13 b2e40
            | exact resolve b2e40 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40
          have b2e68 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e76 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 X0 X0 x
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e42 X0 X1 x
               have i₂ := b2e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b2e18 b2e42
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e42 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e81 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e16 (M.op X0 X1) X2
               have i₂ := b2e42 X0 X1 X2
               grind)
            | exact superpose b2e42 b2e16
            | (have j0 := b2e16 (M.op X0 X1) X2
               grind)
            | (have r₁ := b2e16 (M.op X0 X1) x
               have r₂ := b2e42 X0 X1 x
               grind)
            | exact resolve b2e16 b2e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e85 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b2e81 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e81
          have b2e88 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (M.op (τ X0) X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e32 X0 X1
               have i₂ := b2e18 X1 (τ X0)
               grind)
            | exact superpose b2e18 b2e32
            | (have j1 := b2e18 X1 (τ X0)
               grind)
            | exact resolve b2e32 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32
          have b2e257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e69 (σ X1) (σ X0)
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e69
            | (have j0 := b2e69 (σ X1) (σ X0)
               grind)
            | exact resolve b2e69 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e69
          have b2e672 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e36 (M.op X1 X2) X0
               have i₂ := b2e85 X1 X2 (σ X0)
               grind)
            | exact superpose b2e85 b2e36
            | exact resolve b2e36 b2e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e85
          have b2e692 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e672 X0 X1 X2
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e672
            | exact resolve b2e672 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e672
          have b2e1372 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X1 X0 X2
               have i₂ := b2e76 X0 X3 (M.op X0 X1)
               grind)
            | exact superpose b2e76 b2e13
            | (have j1 := b2e76 X0 X3 X2
               grind)
            | exact resolve b2e13 b2e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e1770 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e88 (σ X0) X1
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e88
            | exact resolve b2e88 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e88
          have b2e1878 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e1770 X0 X1
               have i₂ := b2e19 X1 X0
               grind)
            | exact superpose b2e19 b2e1770
            | (have j0 := b2e1770 X0 X1
               grind)
            | exact resolve b2e1770 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1770
          have b2e2824 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e257 y x
               grind)
            | exact superpose b2e257 b2e20
            | (have j1 := b2e257 y x
               grind)
            | exact resolve b2e20 b2e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e257
          have b2e21866 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (M.op y X1) = (k X1 y) ∨ (M.op y X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e23
               have i₂ := b2e1372 y x X0 X1
               grind)
            | (have i₁ := b2e23
               have i₂ := b2e1372 y X0 x X1
               grind)
            | exact superpose b2e1372 b2e23
            | (have j1 := b2e1372 y X1 x X1
               grind)
            | (have r₁ := b2e23
               have r₂ := b2e1372 x X1 x y
               grind)
            | exact resolve b2e23 b2e1372
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1372
          have b2e22020 : ∀ X1 : G, (M.op y X1) = (k X1 y) ∨ (M.op y X1) = X1 := by
            intro X1
            first
            | (have j0 := b2e21866 x X1
               have j1 := b2e76 y X1 x
               grind)
            | (have r₁ := b2e21866 x X1
               have r₂ := b2e76 y X1 x
               grind)
            | (have r₁ := b2e21866 x X1
               have r₂ := b2e76 x y x
               grind)
            | exact resolve b2e21866 b2e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e76 b2e21866
          have b2e82843 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e2824
               have i₂ := b2e1878 x y
               grind)
            | exact superpose b2e1878 b2e2824
            | (have j1 := b2e1878 x y
               grind)
            | (have r₁ := b2e2824
               have r₂ := b2e1878 x y
               grind)
            | exact resolve b2e2824 b2e1878
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1878 b2e2824
          have b2e82852 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b2e82843
          have b2e82863 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b2e82852
               have r₂ := b2e24
               grind)
            | exact resolve b2e82852 b2e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e82852
          have b2e82868 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b2e82863
               have r₂ := b2e23
               grind)
            | exact resolve b2e82863 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e82863
          have b2e82891 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e692 X0 (σ x) (σ y)
               have i₂ := b2e82868
               grind)
            | exact superpose b2e82868 b2e692
            | exact resolve b2e692 b2e82868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e692 b2e82868
          have b2e82932 : ∀ X0 : G, (k y X0) = X0 ∨ (σ (M.op x y)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b2e82891 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e82891
            | exact resolve b2e82891 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e82891
          have b2e83400 : ∀ X0 : G, (M.op x y) = (τ (σ y)) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e82932 X0
               grind)
            | exact superpose b2e82932 b2e14
            | (have j1 := b2e82932 X0
               grind)
            | exact resolve b2e14 b2e82932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e82932
          have b2e83474 : ∀ X0 : G, y = (M.op x y) ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e83400 X0
               have i₂ := b2e14 y
               grind)
            | exact superpose b2e14 b2e83400
            | (have j0 := b2e83400 X0
               grind)
            | exact resolve b2e83400 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83400
          have b2e83509 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e83474 X0
               grind)
            | (have r₁ := b2e83474 X0
               have r₂ := b2e23
               grind)
            | exact resolve b2e83474 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83474
          have b2e84261 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b2e22020 y
               have i₂ := b2e83509 y
               grind)
            | exact superpose b2e83509 b2e22020
            | (have j0 := b2e22020 y
               grind)
            | exact resolve b2e22020 b2e83509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e22020 b2e83509
          have b2e84262 : y = (M.op y y) := by grind
          clear b2e84261
          have b2e84859 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e42 y y x
               have i₂ := b2e84262
               grind)
            | exact superpose b2e84262 b2e42
            | exact resolve b2e42 b2e84262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42 b2e84262
          have b2e86217 : y ≠ y := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e84859 x
               grind)
            | exact superpose b2e84859 b2e23
            | (have r₁ := b2e23
               have r₂ := b2e84859 x
               grind)
            | exact resolve b2e23 b2e84859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e84859
          have b2e86232 : False := by grind
          exact b2e86232
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e27 : x ≠ x ∨ y = (k x y) := by
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
          have b3e31 : y = (k x y) := by grind
          clear b3e27
          have b3e51 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          have b3e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e51
               have r₂ := b3e22
               grind)
            | exact resolve b3e51 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e51
          have b3e53 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b3e52
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e52
            | exact resolve b3e52 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e52
          have b3e54 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e53
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e53
            | exact resolve b3e53 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e53
          have b3e80 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e54
               grind)
            | exact superpose b3e54 b3e22
            | exact resolve b3e22 b3e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e87 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e80
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e80
            | exact resolve b3e80 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e80
          have b3e90 : False := by grind
          exact b3e90
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : x = (M.op y x) := by grind
            have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : y ≠ (M.op x y) := by grind
            have b4e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : x ≠ x ∨ y = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 x y
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e31 : y = (k x y) := by grind
            clear b4e28
            have b4e39 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
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
            have b4e40 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
            have b4e46 : x = (M.op x y) := by
              first
              | (have i₁ := b4e39 x
                 have i₂ := b4e40 x
                 grind)
              | exact superpose b4e40 b4e39
              | exact resolve b4e39 b4e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e39 b4e40
            have b4e47 : x ≠ y := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e46
                 grind)
              | exact superpose b4e46 b4e25
              | exact resolve b4e25 b4e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e46
            have b4e53 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
            have b4e58 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e53
                 have r₂ := b4e23
                 grind)
              | exact resolve b4e53 b4e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e53
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
            have b4e60 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e59
                 have i₂ := b4e31
                 grind)
              | exact superpose b4e31 b4e59
              | exact resolve b4e59 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31 b4e59
            have b4e86 : y = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 y
                 have i₂ := b4e60
                 grind)
              | exact superpose b4e60 b4e15
              | exact resolve b4e15 b4e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e60
            have b4e87 : x = y := by
              first
              | (have i₁ := b4e86
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e86
              | exact resolve b4e86 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e86
            have b4e92 : False := by grind
            exact b4e92
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : x ≠ x ∨ y = (k x y) := by
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
            have b5e30 : y = (k x y) := by grind
            clear b5e28
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
            have b5e50 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e49
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e49
              | exact resolve b5e49 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e49
            have b5e52 : (σ x) ≠ (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e50
                 grind)
              | exact superpose b5e50 b5e23
              | exact resolve b5e23 b5e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e59 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e52
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e52
              | exact resolve b5e52 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e52
            have b5e61 : False := by grind
            exact b5e61
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : x = (M.op y x) := by grind
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
          have b6e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 (τ X0)
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
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
          have b6e38 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
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
          have b6e40 : ∀ X0 : G, y = (M.op X0 y) := by
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
          have b6e50 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 y X0
               have i₂ := b6e40 X0
               grind)
            | exact superpose b6e40 b6e16
            | (have j0 := b6e16 y X0
               grind)
            | (have r₁ := b6e16 y X0
               have r₂ := b6e40 X0
               grind)
            | exact resolve b6e16 b6e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e40
          have b6e52 : ∀ X0 : G, (k y X0) = X0 := by
            intro X0
            first
            | (have j0 := b6e50 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e50
          have b6e82 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 X1 X0 x
               have i₂ := b6e38 (M.op X0 X1) X0 x
               grind)
            | exact superpose b6e38 b6e13
            | exact resolve b6e13 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e117 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b6e32 X0 y
               have i₂ := b6e52 (τ X0)
               grind)
            | exact superpose b6e52 b6e32
            | exact resolve b6e32 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32 b6e52
          have b6e125 : ∀ X0 : G, (k (σ y) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e117 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e117
            | exact resolve b6e117 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e117
          have b6e132 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
          clear b6e125
          have b6e136 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b6e132
               have i₂ := b6e82 (σ y) (σ y)
               grind)
            | exact superpose b6e82 b6e132
            | exact resolve b6e132 b6e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e82 b6e132
          have b6e137 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b6e136
          have b6e424 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b6e38 (σ y) (σ y) x
               have i₂ := b6e137
               grind)
            | exact superpose b6e137 b6e38
            | exact resolve b6e38 b6e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38 b6e137
          have b6e452 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b6e26
               have i₂ := b6e424 (σ x)
               grind)
            | exact superpose b6e424 b6e26
            | (have r₁ := b6e26
               have r₂ := b6e424 (σ x)
               grind)
            | exact resolve b6e26 b6e424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e424
          have b6e453 : False := by grind
          exact b6e453
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
            have b7e25 : y ≠ (M.op x y) := by grind
            have b7e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : x ≠ x ∨ y = (k x y) := by
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
            have b7e30 : y = (k x y) := by grind
            clear b7e28
            have b7e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b7e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k (τ X0) X1)
                 have i₂ := b7e31 X0 X1
                 grind)
              | exact superpose b7e31 b7e15
              | exact resolve b7e15 b7e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e37 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
              intro X0
              first
              | (have i₁ := b7e14 x y X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e38 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
            have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X2 (M.op (M.op X1 X0) X1) X3
                 have i₂ := b7e14 X0 X1 (M.op (M.op (M.op X1 X0) X1) X2)
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b7e40 X0 X1 x X3
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e40
              | exact resolve b7e40 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e43 : x = (M.op x y) := by
              first
              | (have i₁ := b7e37 x
                 have i₂ := b7e38 x
                 grind)
              | exact superpose b7e38 b7e37
              | exact resolve b7e37 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37 b7e38
            have b7e44 : x ≠ y := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e43
                 grind)
              | exact superpose b7e43 b7e25
              | exact resolve b7e25 b7e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43
            have b7e49 : y = (k y x) ∨ y = (M.op x y) := by grind
            have b7e53 : y = (k y x) := by
              first
              | (have r₁ := b7e49
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e49 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e49
            have b7e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b7e102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e17 (M.op X0 X1) X2
                 have i₂ := b7e42 X0 X1 X2
                 grind)
              | exact superpose b7e42 b7e17
              | (have j0 := b7e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b7e17 (M.op X0 X1) x
                 have r₂ := b7e42 X0 X1 x
                 grind)
              | exact resolve b7e17 b7e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e42
            have b7e106 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b7e102 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e102
            have b7e403 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b7e65 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e65
            have b7e404 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b7e403
                 have r₂ := b7e23
                 grind)
              | exact resolve b7e403 b7e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e403
            have b7e405 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b7e404
                 have i₂ := b7e20 x y
                 grind)
              | exact superpose b7e20 b7e404
              | exact resolve b7e404 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e404
            have b7e406 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e405
                 have i₂ := b7e30
                 grind)
              | exact superpose b7e30 b7e405
              | exact resolve b7e405 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e30 b7e405
            have b7e414 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e106 (σ y) (σ x) X0
                 have i₂ := b7e406
                 grind)
              | exact superpose b7e406 b7e106
              | exact resolve b7e106 b7e406
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e106 b7e406
            have b7e684 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b7e36 (σ y) X0
                 have i₂ := b7e414 (σ X0)
                 grind)
              | exact superpose b7e414 b7e36
              | exact resolve b7e36 b7e414
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e414
            have b7e692 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b7e684 X0
                 have i₂ := b7e15 y
                 grind)
              | exact superpose b7e15 b7e684
              | exact resolve b7e684 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e684
            have b7e698 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e692 X0
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e692
              | exact resolve b7e692 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e692
            have b7e708 : x = y := by
              first
              | (have i₁ := b7e53
                 have i₂ := b7e698 x
                 grind)
              | exact superpose b7e698 b7e53
              | exact resolve b7e53 b7e698
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e53 b7e698
            have b7e723 : False := by grind
            exact b7e723
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b8e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b8e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
            have b8e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : x ≠ x ∨ y = (k x y) := by
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
            have b8e29 : y = (k x y) := by grind
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
            have b8e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            have b8e36 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b8e34 X0 X1 x X3
                 have i₂ := b8e14 X0 X1 x
                 grind)
              | exact superpose b8e14 b8e34
              | exact resolve b8e34 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e34
            have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            have b8e70 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 X0 x
                 have i₂ := b8e36 (M.op X0 X1) X0 x
                 grind)
              | exact superpose b8e36 b8e14
              | exact resolve b8e14 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e72 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e17 (M.op X0 X1) X2
                 have i₂ := b8e36 X0 X1 X2
                 grind)
              | exact superpose b8e36 b8e17
              | (have j0 := b8e17 (M.op X0 X1) X2
                 grind)
              | (have r₁ := b8e17 (M.op X0 X1) x
                 have r₂ := b8e36 X0 X1 x
                 grind)
              | exact resolve b8e17 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e76 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
              intro X0 X1 X2
              first
              | (have j0 := b8e72 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e72
            have b8e83 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b8e15 (k (τ X0) X1)
                 have i₂ := b8e30 X0 X1
                 grind)
              | exact superpose b8e30 b8e15
              | exact resolve b8e15 b8e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e30
            have b8e378 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e60 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e60
            have b8e379 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e378
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e378 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e378
            have b8e380 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e379
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e379
              | exact resolve b8e379 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e379
            have b8e381 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e380
                 have i₂ := b8e29
                 grind)
              | exact superpose b8e29 b8e380
              | exact resolve b8e380 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e380
            have b8e389 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e76 (σ y) (σ x) X0
                 have i₂ := b8e381
                 grind)
              | exact superpose b8e381 b8e76
              | exact resolve b8e76 b8e381
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e76 b8e381
            have b8e651 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b8e83 (σ y) X0
                 have i₂ := b8e389 (σ X0)
                 grind)
              | exact superpose b8e389 b8e83
              | exact resolve b8e83 b8e389
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e83 b8e389
            have b8e659 : ∀ X0 : G, (τ (σ X0)) = (k y X0) := by
              intro X0
              first
              | (have i₁ := b8e651 X0
                 have i₂ := b8e15 y
                 grind)
              | exact superpose b8e15 b8e651
              | exact resolve b8e651 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e651
            have b8e667 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b8e659 X0
                 have i₂ := b8e15 X0
                 grind)
              | exact superpose b8e15 b8e659
              | exact resolve b8e659 b8e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e659
            have b8e682 : y = (M.op y y) ∨ y = (M.op (M.op y y) y) := by grind
            clear b8e667
            have b8e689 : y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b8e682
                 have i₂ := b8e70 y y
                 grind)
              | exact superpose b8e70 b8e682
              | exact resolve b8e682 b8e70
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e70 b8e682
            have b8e690 : y = (M.op y y) := by grind
            clear b8e689
            have b8e727 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e36 y y x
                 have i₂ := b8e690
                 grind)
              | exact superpose b8e690 b8e36
              | exact resolve b8e36 b8e690
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36 b8e690
            have b8e891 : y ≠ y := by
              first
              | (have i₁ := b8e25
                 have i₂ := b8e727 x
                 grind)
              | exact superpose b8e727 b8e25
              | (have r₁ := b8e25
                 have r₂ := b8e727 x
                 grind)
              | exact resolve b8e25 b8e727
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e727
            have b8e893 : False := by grind
            exact b8e893
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b9e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b9e30 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b9e29
          have b9e32 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b9e30
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e30
            | exact resolve b9e30 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e37 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e32
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e38 : y = (k x y) := by
            first
            | (have i₁ := b9e37
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e37
            | exact resolve b9e37 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e48 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b9e50 : x = (k x y) := by
            first
            | (have r₁ := b9e48
               have r₂ := b9e21
               grind)
            | exact resolve b9e48 b9e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e48
          have b9e52 : x = y := by
            first
            | (have i₁ := b9e38
               have i₂ := b9e50
               grind)
            | exact superpose b9e50 b9e38
            | exact resolve b9e38 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e50
          have b9e74 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e23
               have i₂ := b9e52
               grind)
            | exact superpose b9e52 b9e23
            | exact resolve b9e23 b9e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e76 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e52
               grind)
            | exact superpose b9e52 b9e26
            | exact resolve b9e26 b9e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26 b9e52
          have b9e81 : False := by grind
          exact b9e81
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : x ≠ (M.op y x) := by grind
            have b10e23 : y = (M.op x x) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : y ≠ (M.op x y) := by grind
            have b10e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b10e30
            have b10e32 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b10e31
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e31
              | exact resolve b10e31 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e31
            have b10e33 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e32
                 grind)
              | exact superpose b10e32 b10e15
              | exact resolve b10e15 b10e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e34 : y = (k x y) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e33
              | exact resolve b10e33 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e55 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b10e57 : x = (k x y) := by
              first
              | (have r₁ := b10e55
                 have r₂ := b10e22
                 grind)
              | exact resolve b10e55 b10e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e55
            have b10e59 : x = y := by
              first
              | (have i₁ := b10e34
                 have i₂ := b10e57
                 grind)
              | exact superpose b10e57 b10e34
              | exact resolve b10e34 b10e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34 b10e57
            have b10e83 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e59
                 grind)
              | exact superpose b10e59 b10e25
              | exact resolve b10e25 b10e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e84 : x = (M.op x x) := by
              first
              | (have i₁ := b10e26
                 have i₂ := b10e59
                 grind)
              | exact superpose b10e59 b10e26
              | exact resolve b10e26 b10e59
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e59
            have b10e92 : False := by grind
            exact b10e92
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
            have b11e29 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b11e30 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b11e29
            have b11e31 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e30
              | exact resolve b11e30 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e15
              | exact resolve b11e15 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : y = (k x y) := by
              first
              | (have i₁ := b11e32
                 have i₂ := b11e15 y
                 grind)
              | exact superpose b11e15 b11e32
              | exact resolve b11e32 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e51 : x = (k x y) ∨ x = (M.op y x) := by grind
            have b11e54 : x = (k x y) := by
              first
              | (have r₁ := b11e51
                 have r₂ := b11e22
                 grind)
              | exact resolve b11e51 b11e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e51
            have b11e56 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e54
                 grind)
              | exact superpose b11e54 b11e33
              | exact resolve b11e33 b11e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e54
            have b11e81 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e56
                 grind)
              | exact superpose b11e56 b11e26
              | exact resolve b11e26 b11e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e89 : x ≠ y := by
              first
              | (have i₁ := b11e81
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e81
              | exact resolve b11e81 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e81
            have b11e93 : False := by grind
            exact b11e93
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
            have b12e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            have b12e42 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e40 X0 X1 x X3
                 have i₂ := b12e14 X0 X1 x
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e109 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e42 (σ x) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e42
              | exact resolve b12e42 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e172 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e109 (σ x)
                 grind)
              | exact superpose b12e109 b12e28
              | (have r₁ := b12e28
                 have r₂ := b12e109 (σ x)
                 grind)
              | exact resolve b12e28 b12e109
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28 b12e109
            have b12e180 : False := by grind
            exact b12e180
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
              have b13e43 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
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
              have b13e47 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b13e43 x X1
                   have i₂ := b13e38 x
                   grind)
                | exact superpose b13e38 b13e43
                | exact resolve b13e43 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38 b13e43
              have b13e75 : y ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e47 x
                   grind)
                | exact superpose b13e47 b13e27
                | (have r₁ := b13e27
                   have r₂ := b13e47 x
                   grind)
                | exact resolve b13e27 b13e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47
              have b13e82 : False := by grind
              exact b13e82
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e39 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b14e45 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X0 (M.op y x) X1
                   have i₂ := b14e39 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b14e39 b14e15
                | exact resolve b14e15 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e49 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b14e45 x X1
                   have i₂ := b14e39 x
                   grind)
                | exact superpose b14e39 b14e45
                | exact resolve b14e45 b14e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e45
              have b14e78 : y ≠ y := by
                first
                | (have i₁ := b14e27
                   have i₂ := b14e49 x
                   grind)
                | exact superpose b14e49 b14e27
                | (have r₁ := b14e27
                   have r₂ := b14e49 x
                   grind)
                | exact resolve b14e27 b14e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e49
              have b14e85 : False := by grind
              exact b14e85
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b15e23 : y = (M.op x x) := by grind
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
            have b15e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 (τ X0)
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
            have b15e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            have b15e39 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e37 X0 X1 x X3
                 have i₂ := b15e14 X0 X1 x
                 grind)
              | exact superpose b15e14 b15e37
              | exact resolve b15e37 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e40 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 (M.op y x) X1
                 have i₂ := b15e34 (M.op (M.op y x) X0)
                 grind)
              | exact superpose b15e34 b15e14
              | exact resolve b15e14 b15e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e44 : ∀ X1 : G, y = (M.op X1 y) := by
              intro X1
              first
              | (have i₁ := b15e40 x X1
                 have i₂ := b15e34 x
                 grind)
              | exact superpose b15e34 b15e40
              | exact resolve b15e40 b15e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34 b15e40
            have b15e71 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 y X0
                 have i₂ := b15e44 X0
                 grind)
              | exact superpose b15e44 b15e17
              | (have j0 := b15e17 y X0
                 grind)
              | (have r₁ := b15e17 y x
                 have r₂ := b15e44 x
                 grind)
              | exact resolve b15e17 b15e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e44
            have b15e72 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have j0 := b15e71 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e71
            have b15e108 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X0 x
                 have i₂ := b15e39 (M.op X0 X1) X0 x
                 grind)
              | exact superpose b15e39 b15e14
              | exact resolve b15e14 b15e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e133 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b15e33 X0 y
                 have i₂ := b15e72 (τ X0)
                 grind)
              | exact superpose b15e72 b15e33
              | exact resolve b15e33 b15e72
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e33 b15e72
            have b15e141 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e133 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e133
              | exact resolve b15e133 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e133
            have b15e148 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
            clear b15e141
            have b15e152 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b15e148
                 have i₂ := b15e108 (σ y) (σ y)
                 grind)
              | exact superpose b15e108 b15e148
              | exact resolve b15e148 b15e108
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e108 b15e148
            have b15e153 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b15e152
            have b15e446 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b15e39 (σ y) (σ y) x
                 have i₂ := b15e153
                 grind)
              | exact superpose b15e153 b15e39
              | exact resolve b15e39 b15e153
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e39 b15e153
            have b15e456 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b15e28
                 have i₂ := b15e446 (σ x)
                 grind)
              | exact superpose b15e446 b15e28
              | (have r₁ := b15e28
                 have r₂ := b15e446 (σ x)
                 grind)
              | exact resolve b15e28 b15e446
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e446
            have b15e474 : False := by grind
            exact b15e474
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b16e40 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X0 (M.op y x) X1
                   have i₂ := b16e34 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b16e34 b16e15
                | exact resolve b16e15 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e44 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b16e40 x X1
                   have i₂ := b16e34 x
                   grind)
                | exact superpose b16e34 b16e40
                | exact resolve b16e40 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34 b16e40
              have b16e68 : y ≠ y := by
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
              have b16e75 : False := by grind
              exact b16e75
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e27 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e37 : ∀ X0 : G, y = (M.op X0 (M.op y x)) := by
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
              have b17e42 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X0 (M.op y x) X1
                   have i₂ := b17e37 (M.op (M.op y x) X0)
                   grind)
                | exact superpose b17e37 b17e15
                | exact resolve b17e15 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e46 : ∀ X1 : G, y = (M.op X1 y) := by
                intro X1
                first
                | (have i₁ := b17e42 x X1
                   have i₂ := b17e37 x
                   grind)
                | exact superpose b17e37 b17e42
                | exact resolve b17e42 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37 b17e42
              have b17e71 : y ≠ y := by
                first
                | (have i₁ := b17e27
                   have i₂ := b17e46 x
                   grind)
                | exact superpose b17e46 b17e27
                | (have r₁ := b17e27
                   have r₂ := b17e46 x
                   grind)
                | exact resolve b17e27 b17e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e78 : False := by grind
              exact b17e78
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e43 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
          have b18e45 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b18e43 X0 X1 x X3
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e43
            | exact resolve b18e43 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e43
          have b18e86 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e45 (σ y) (σ x) x
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e45
            | exact resolve b18e45 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e91 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b18e13 X1 X0 x
               have i₂ := b18e45 (M.op X0 X1) X0 x
               grind)
            | exact superpose b18e45 b18e13
            | exact resolve b18e13 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e359 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e16 (σ x) X0
               have i₂ := b18e86 X0
               grind)
            | exact superpose b18e86 b18e16
            | (have j0 := b18e16 (σ x) X0
               grind)
            | (have r₁ := b18e16 (σ x) X0
               have r₂ := b18e86 X0
               grind)
            | exact resolve b18e16 b18e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e86
          have b18e362 : ∀ X0 : G, (k (σ x) X0) = X0 := by
            intro X0
            first
            | (have j0 := b18e359 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e359
          have b18e401 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b18e19 x X0
               have i₂ := b18e362 (σ X0)
               grind)
            | exact superpose b18e362 b18e19
            | exact resolve b18e19 b18e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e362
          have b18e539 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b18e14 (k x X0)
               have i₂ := b18e401 X0
               grind)
            | exact superpose b18e401 b18e14
            | exact resolve b18e14 b18e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e401
          have b18e548 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b18e539 X0
               have i₂ := b18e14 X0
               grind)
            | exact superpose b18e14 b18e539
            | exact resolve b18e539 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e539
          have b18e615 : x = (M.op x x) ∨ x = (M.op (M.op x x) x) := by grind
          clear b18e548
          have b18e625 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b18e615
               have i₂ := b18e91 x x
               grind)
            | exact superpose b18e91 b18e615
            | exact resolve b18e615 b18e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e91 b18e615
          have b18e626 : x = (M.op x x) := by grind
          clear b18e625
          have b18e686 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e45 x x x
               have i₂ := b18e626
               grind)
            | exact superpose b18e626 b18e45
            | exact resolve b18e45 b18e626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45 b18e626
          have b18e736 : x ≠ x := by
            first
            | (have i₁ := b18e21
               have i₂ := b18e686 y
               grind)
            | exact superpose b18e686 b18e21
            | (have r₁ := b18e21
               have r₂ := b18e686 y
               grind)
            | exact resolve b18e21 b18e686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e686
          have b18e754 : False := by grind
          exact b18e754
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b19e22 : x ≠ (M.op y x) := by grind
            have b19e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e40 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
            have b19e46 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 (M.op x y) X1
                 have i₂ := b19e40 (M.op (M.op x y) X0)
                 grind)
              | exact superpose b19e40 b19e14
              | exact resolve b19e14 b19e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e50 : ∀ X1 : G, x = (M.op X1 x) := by
              intro X1
              first
              | (have i₁ := b19e46 x X1
                 have i₂ := b19e40 x
                 grind)
              | exact superpose b19e40 b19e46
              | exact resolve b19e46 b19e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e40 b19e46
            have b19e74 : x ≠ x := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e50 y
                 grind)
              | exact superpose b19e50 b19e22
              | (have r₁ := b19e22
                 have r₂ := b19e50 y
                 grind)
              | exact resolve b19e22 b19e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e50
            have b19e81 : False := by grind
            exact b19e81
          · have b20e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : x ≠ (M.op y x) := by grind
            have b20e23 : y ≠ (M.op x x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b20e25 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b20e29 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b20e28
            have b20e30 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e29
              | exact resolve b20e29 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e30
                 grind)
              | exact superpose b20e30 b20e15
              | exact resolve b20e15 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e32 : y = (k x y) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e31
              | exact resolve b20e31 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e45 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            have b20e47 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b20e45 X0 X1 x X3
                 have i₂ := b20e14 X0 X1 x
                 grind)
              | exact superpose b20e14 b20e45
              | exact resolve b20e45 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e45
            have b20e78 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
              first
              | (have i₁ := b20e32
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e32
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e32 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e90 : y = (M.op y x) ∨ x = (M.op y x) := by
              first
              | (have r₁ := b20e78
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e78 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e78
            have b20e93 : y = (M.op y x) := by
              first
              | (have r₁ := b20e90
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e90 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90
            have b20e96 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b20e47 y x x
                 have i₂ := b20e93
                 grind)
              | exact superpose b20e93 b20e47
              | exact resolve b20e47 b20e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e47 b20e93
            have b20e119 : y ≠ y := by
              first
              | (have i₁ := b20e25
                 have i₂ := b20e96 x
                 grind)
              | exact superpose b20e96 b20e25
              | (have r₁ := b20e25
                 have r₂ := b20e96 x
                 grind)
              | exact resolve b20e25 b20e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e96
            have b20e127 : False := by grind
            exact b20e127
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
              have b22e39 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
              have b22e45 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X0 (M.op x y) X1
                   have i₂ := b22e39 (M.op (M.op x y) X0)
                   grind)
                | exact superpose b22e39 b22e15
                | exact resolve b22e15 b22e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e49 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b22e45 x X1
                   have i₂ := b22e39 x
                   grind)
                | exact superpose b22e39 b22e45
                | exact resolve b22e45 b22e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39 b22e45
              have b22e78 : x ≠ x := by
                first
                | (have i₁ := b22e23
                   have i₂ := b22e49 y
                   grind)
                | exact superpose b22e49 b22e23
                | (have r₁ := b22e23
                   have r₂ := b22e49 y
                   grind)
                | exact resolve b22e23 b22e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49
              have b22e85 : False := by grind
              exact b22e85
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
              have b23e49 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
              have b23e52 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e49
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e49 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e49
              have b23e53 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e52
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e52
                | exact resolve b23e52 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52
              have b23e56 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e53
                   grind)
                | exact superpose b23e53 b23e16
                | exact resolve b23e16 b23e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e53
              have b23e57 : x = (k x y) := by
                first
                | (have i₁ := b23e56
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e56
                | exact resolve b23e56 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e56
              have b23e79 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e57
                   grind)
                | exact superpose b23e57 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e57
              have b23e80 : x = (M.op y x) ∨ y = (M.op x x) := by grind
              clear b23e79
              have b23e82 : y = (M.op x x) := by
                first
                | (have r₁ := b23e80
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e80 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e80
              have b23e84 : False := by grind
              exact b23e84
        · rcases eq_or_ne (M.op x y) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
              intro X0 X1 X2
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
            have b24e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
            have b24e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X0) X1)) = (M.op X3 (M.op X0 X1)) := by
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
            have b24e37 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op X3 (M.op X0 X1)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b24e35 X0 X1 x X3
                 have i₂ := b24e14 X0 X1 x
                 grind)
              | exact superpose b24e14 b24e35
              | exact resolve b24e35 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35
            have b24e64 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b24e37 x y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e37
              | exact resolve b24e37 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e71 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X0 x
                 have i₂ := b24e37 (M.op X0 X1) X0 x
                 grind)
              | exact superpose b24e37 b24e14
              | exact resolve b24e14 b24e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e91 : ∀ X0 : G, y ≠ y ∨ (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e17 y X0
                 have i₂ := b24e64 X0
                 grind)
              | exact superpose b24e64 b24e17
              | (have j0 := b24e17 y X0
                 grind)
              | (have r₁ := b24e17 y X0
                 have r₂ := b24e64 X0
                 grind)
              | exact resolve b24e17 b24e64
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e64
            have b24e92 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have j0 := b24e91 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e91
            have b24e109 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b24e32 X0 y
                 have i₂ := b24e92 (τ X0)
                 grind)
              | exact superpose b24e92 b24e32
              | exact resolve b24e32 b24e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32 b24e92
            have b24e110 : ∀ X0 : G, (k (σ y) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e109 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e109
              | exact resolve b24e109 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e109
            have b24e229 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by grind
            clear b24e110
            have b24e233 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b24e229
                 have i₂ := b24e71 (σ y) (σ y)
                 grind)
              | exact superpose b24e71 b24e229
              | exact resolve b24e229 b24e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e71 b24e229
            have b24e234 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b24e233
            have b24e390 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e37 (σ y) (σ y) x
                 have i₂ := b24e234
                 grind)
              | exact superpose b24e234 b24e37
              | exact resolve b24e37 b24e234
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e37 b24e234
            have b24e488 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b24e28
                 have i₂ := b24e390 (σ x)
                 grind)
              | exact superpose b24e390 b24e28
              | (have r₁ := b24e28
                 have r₂ := b24e390 (σ x)
                 grind)
              | exact resolve b24e28 b24e390
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e28 b24e390
            have b24e507 : False := by grind
            exact b24e507
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b25e23 : x ≠ (M.op y x) := by grind
              have b25e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e37 : ∀ X0 : G, x = (M.op X0 (M.op x y)) := by
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
              have b25e42 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X1 x) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X0 (M.op x y) X1
                   have i₂ := b25e37 (M.op (M.op x y) X0)
                   grind)
                | exact superpose b25e37 b25e15
                | exact resolve b25e15 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e46 : ∀ X1 : G, x = (M.op X1 x) := by
                intro X1
                first
                | (have i₁ := b25e42 x X1
                   have i₂ := b25e37 x
                   grind)
                | exact superpose b25e37 b25e42
                | exact resolve b25e42 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e42
              have b25e71 : x ≠ x := by
                first
                | (have i₁ := b25e23
                   have i₂ := b25e46 y
                   grind)
                | exact superpose b25e46 b25e23
                | (have r₁ := b25e23
                   have r₂ := b25e46 y
                   grind)
                | exact resolve b25e23 b25e46
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e46
              have b25e78 : False := by grind
              exact b25e78
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X1 X0) X1)) := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
              have b26e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b26e27 : y ≠ (M.op x y) := by grind
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
              have b26e39 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e15 X1 X0 x
                   have i₂ := b26e35 (M.op X0 X1) X0 x
                   grind)
                | exact superpose b26e35 b26e15
                | exact resolve b26e15 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e42 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 (M.op X0 X1) X2
                   have i₂ := b26e35 X0 X1 X2
                   grind)
                | exact superpose b26e35 b26e18
                | (have j0 := b26e18 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e18 (M.op X0 X1) x
                   have r₂ := b26e35 X0 X1 x
                   grind)
                | exact resolve b26e18 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e43 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e42 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e42
              have b26e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
              have b26e58 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e60 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) = X0 ∨ (M.op X0 X1) = X1 := by
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
              have b26e66 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (k X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e58 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58
              have b26e88 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e30 X0 X1
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30
              have b26e231 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e66 (σ X1) (σ X0)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e66
                | (have j0 := b26e66 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e66 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e66
              have b26e294 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k (τ (M.op X1 X2)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e88 (M.op X1 X2) X0
                   have i₂ := b26e43 X1 X2 (σ X0)
                   grind)
                | exact superpose b26e43 b26e88
                | exact resolve b26e88 b26e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e43 b26e88
              have b26e298 : ∀ X0 X1 X2 : G, (k (τ (M.op X1 X2)) X0) = X0 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e294 X0 X1 X2
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e294
                | exact resolve b26e294 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e294
              have b26e331 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) (τ (M.op X0 X1))) := by
                intro X0 X1
                grind
              clear b26e298
              have b26e338 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e331 X0 X1
                   have i₂ := b26e39 (τ (M.op X0 X1)) (τ (M.op X0 X1))
                   grind)
                | exact superpose b26e39 b26e331
                | (have j0 := b26e331 X0 X1
                   grind)
                | exact resolve b26e331 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e39 b26e331
              have b26e339 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have j0 := b26e338 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e338
              have b26e449 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op X2 (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (σ X1) (σ X1) x
                   have i₂ := b26e56 X0 X1
                   grind)
                | exact superpose b26e56 b26e35
                | (have j1 := b26e56 X0 X1
                   grind)
                | exact resolve b26e35 b26e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e56
              have b26e1074 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X0 X3) = (k X3 X0) ∨ (M.op X0 X3) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e15 X1 X0 X2
                   have i₂ := b26e60 X0 X3 (M.op X0 X1)
                   grind)
                | exact superpose b26e60 b26e15
                | (have j1 := b26e60 X0 X3 X2
                   grind)
                | exact resolve b26e15 b26e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e2466 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e231 y x
                   grind)
                | exact superpose b26e231 b26e22
                | (have j1 := b26e231 y x
                   grind)
                | exact resolve b26e22 b26e231
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e231
              have b26e2669 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e449 x X0 (σ y)
                   grind)
                | exact superpose b26e449 b26e25
                | (have j1 := b26e449 x X0 x
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e449 x x (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e449 y x x
                   grind)
                | exact resolve b26e25 b26e449
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e449
              have b26e2700 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2669 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2669
              have b26e14564 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e35 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e339 X0 X1
                   grind)
                | exact superpose b26e339 b26e35
                | exact resolve b26e35 b26e339
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e339
              have b26e19429 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 x)) ∨ (σ X0) = (M.op (σ x) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e2700 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2700
              have b26e20167 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e23
                   have i₂ := b26e1074 x y X0 X1
                   grind)
                | (have i₁ := b26e23
                   have i₂ := b26e1074 x X0 y X1
                   grind)
                | exact superpose b26e1074 b26e23
                | (have j1 := b26e1074 x X1 x X1
                   grind)
                | (have r₁ := b26e23
                   have r₂ := b26e1074 y X1 x x
                   grind)
                | exact resolve b26e23 b26e1074
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1074
              have b26e20338 : ∀ X1 : G, (M.op x X1) = (k X1 x) ∨ (M.op x X1) = X1 := by
                intro X1
                first
                | (have j0 := b26e20167 x X1
                   have j1 := b26e60 x X1 x
                   grind)
                | (have r₁ := b26e20167 x X1
                   have r₂ := b26e60 x X1 x
                   grind)
                | (have r₁ := b26e20167 x X1
                   have r₂ := b26e60 x x x
                   grind)
                | exact resolve b26e20167 b26e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60 b26e20167
              have b26e24672 : ∀ X0 : G, (σ X0) ≠ (σ (M.op x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (M.op x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b26e19429 X0
                   have i₂ := b26e20338 X0
                   grind)
                | exact superpose b26e20338 b26e19429
                | (have j0 := b26e19429 X0
                   have j1 := b26e20338 X0
                   grind)
                | exact resolve b26e19429 b26e20338
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19429
              have b26e79108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b26e2466
                   have i₂ := b26e20338 y
                   grind)
                | exact superpose b26e20338 b26e2466
                | (have j1 := b26e20338 y
                   grind)
                | exact resolve b26e2466 b26e20338
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2466 b26e20338
              have b26e79136 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
              clear b26e79108
              have b26e79152 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
                first
                | (have j1 := b26e24672 y
                   grind)
                | (have r₁ := b26e79136
                   have r₂ := b26e24672 y
                   grind)
                | exact resolve b26e79136 b26e24672
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e24672 b26e79136
              have b26e79164 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e79152
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e79152 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79152
              have b26e79210 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) := by
                intro X0
                first
                | (have i₁ := b26e14564 (σ x) (σ y) x
                   have i₂ := b26e79164
                   grind)
                | exact superpose b26e79164 b26e14564
                | exact resolve b26e14564 b26e79164
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e14564 b26e79164
              have b26e79224 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b26e79210 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e79210
                | exact resolve b26e79210 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79210
              have b26e79286 : y ≠ y := by
                first
                | (have i₁ := b26e27
                   have i₂ := b26e79224 x
                   grind)
                | exact superpose b26e79224 b26e27
                | (have r₁ := b26e27
                   have r₂ := b26e79224 x
                   grind)
                | exact resolve b26e27 b26e79224
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e79224
              have b26e79344 : False := by grind
              exact b26e79344

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
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
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
          intro X0 X1 X2 X3
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y x) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e35 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 y X0 X1 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 x X0 X1 y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X3 X0) X1) X4 x
             have i₂ := b0e12 X0 X1 (M.op x X2) X3
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b0e37 X0 X1 x x X4
             have i₂ := b0e12 X0 X1 x x
             grind)
          | exact superpose b0e12 b0e37
          | exact resolve b0e37 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e37
        have b0e42 : ∀ X0 : G, (M.op y y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b0e35 y X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e35
          | exact resolve b0e35 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e35
        have b0e69 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op y y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 x X0 X1 x
             have i₂ := b0e42 x
             grind)
          | exact superpose b0e42 b0e12
          | exact resolve b0e12 b0e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e77 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e69 X0 x
             have i₂ := b0e12 y X0 x y
             grind)
          | exact superpose b0e12 b0e69
          | exact resolve b0e69 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e69
        have b0e84 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e36 x X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e36
          | exact resolve b0e36 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e105 : ∀ X0 : G, (M.op y x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e84 X0
             have i₂ := b0e77 x
             grind)
          | exact superpose b0e77 b0e84
          | exact resolve b0e84 b0e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e77 b0e84
        have b0e111 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e105 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e105
          | exact resolve b0e105 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e105
        have b0e119 : x = y := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e111 x
             grind)
          | exact superpose b0e111 b0e22
          | exact resolve b0e22 b0e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e111
        have b0e133 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e39 (σ y) (σ x) x
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e39
          | exact resolve b0e39 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e157 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e119
             grind)
          | exact superpose b0e119 b0e23
          | exact resolve b0e23 b0e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e119
        have b0e163 : False := by grind
        exact b0e163
      · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b1e43 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b1e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b1e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b1e43 X0 X1 x x X4
               have i₂ := b1e13 X0 X1 x x
               grind)
            | exact superpose b1e13 b1e43
            | exact resolve b1e43 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e43
          have b1e117 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e45 (σ y) (σ x) x
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e45
            | exact resolve b1e45 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e45
          have b1e143 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e26
               have i₂ := b1e117 (σ x)
               grind)
            | exact superpose b1e117 b1e26
            | (have r₁ := b1e26
               have r₂ := b1e117 (σ x)
               grind)
            | exact resolve b1e26 b1e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e26 b1e117
          have b1e147 : False := by grind
          exact b1e147
        · have b2e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b2e21 : y = (M.op y x) := by grind
          have b2e24 : y ≠ (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e36 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 x X0 X1 y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b2e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b2e39 X0 X1 x x X4
               have i₂ := b2e13 X0 X1 x x
               grind)
            | exact superpose b2e13 b2e39
            | exact resolve b2e39 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39
          have b2e43 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e36 x X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e36
            | exact resolve b2e36 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e55 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b2e43 X1
               have i₂ := b2e43 X0
               grind)
            | exact superpose b2e43 b2e43
            | exact resolve b2e43 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43
          have b2e92 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e55 x X0
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e55 X0 x
               grind)
            | exact superpose b2e55 b2e24
            | exact resolve b2e24 b2e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e55
          have b2e107 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e41 y x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e41
            | exact resolve b2e41 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e41
          have b2e120 : False := by grind
          exact b2e120
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op y x) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b3e54 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b3e55 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b3e54
          have b3e56 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e55
               have r₂ := b3e25
               grind)
            | exact resolve b3e55 b3e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e55
          have b3e57 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b3e56
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e56
            | exact resolve b3e56 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e56
          have b3e58 : (σ x) = (σ y) := by
            first
            | (have i₁ := b3e57
               have i₂ := b3e31
               grind)
            | exact superpose b3e31 b3e57
            | exact resolve b3e57 b3e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e31 b3e57
          have b3e59 : False := by grind
          exact b3e59
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b4e23
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e23
              | exact resolve b4e23 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : y ≠ y ∨ x = (k x y) := by
              first
              | (have i₁ := b4e17 x y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e17
              | (have j0 := b4e17 x y
                 grind)
              | (have r₁ := b4e17 x y
                 have r₂ := b4e22
                 grind)
              | exact resolve b4e17 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e33 : x = (k x y) := by grind
            clear b4e30
            have b4e53 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b4e56 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b4e53
            have b4e59 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b4e56
                 have r₂ := b4e28
                 grind)
              | exact resolve b4e56 b4e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e56
            have b4e60 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b4e59
                 have i₂ := b4e20 x y
                 grind)
              | exact superpose b4e20 b4e59
              | exact resolve b4e59 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e59
            have b4e61 : (σ x) = (σ y) := by
              first
              | (have i₁ := b4e60
                 have i₂ := b4e33
                 grind)
              | exact superpose b4e33 b4e60
              | exact resolve b4e60 b4e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33 b4e60
            have b4e62 : False := by grind
            exact b4e62
          · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op y x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e23
              | exact resolve b5e23 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e28 : y ≠ y ∨ x = (k x y) := by
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
            have b5e30 : x = (k x y) := by grind
            clear b5e28
            have b5e50 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b5e53 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b5e50
            have b5e54 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e53
                 have r₂ := b5e27
                 grind)
              | exact resolve b5e53 b5e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e53
            have b5e55 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e54
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e54
              | exact resolve b5e54 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e54
            have b5e56 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e55
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e55
              | exact resolve b5e55 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e55
            have b5e57 : False := by grind
            exact b5e57
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b6e20
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e20
            | exact resolve b6e20 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e26 : y ≠ y ∨ x = (k x y) := by
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
          have b6e29 : x = (k x y) := by grind
          clear b6e26
          have b6e32 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 x X0 X1 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e33 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 y X0 X1 x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b6e32 x X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e32
            | exact resolve b6e32 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e61 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b6e32 y X0
               have i₂ := b6e39 y
               grind)
            | exact superpose b6e39 b6e32
            | exact resolve b6e32 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e32 b6e39
          have b6e62 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b6e61 x
               have i₂ := b6e33 x x
               grind)
            | exact superpose b6e33 b6e61
            | exact resolve b6e61 b6e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33 b6e61
          have b6e68 : y = (M.op x y) := by
            first
            | (have i₁ := b6e62
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e62
            | exact resolve b6e62 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e71 : x = y := by
            first
            | (have i₁ := b6e68
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e68
            | exact resolve b6e68 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e68
          have b6e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 X1 X0
               have i₂ := b6e18 (σ X1) (σ X0)
               grind)
            | exact superpose b6e18 b6e19
            | (have j1 := b6e18 (σ X1) (σ X0)
               grind)
            | exact resolve b6e19 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e86 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e25
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e25
            | exact resolve b6e25 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e25
          have b6e88 : x = (k x x) := by
            first
            | (have i₁ := b6e29
               have i₂ := b6e71
               grind)
            | exact superpose b6e71 b6e29
            | exact resolve b6e29 b6e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e29 b6e71
          have b6e497 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e86
               have i₂ := b6e75 x x
               grind)
            | exact superpose b6e75 b6e86
            | (have j1 := b6e75 x x
               grind)
            | (have r₁ := b6e86
               have r₂ := b6e75 x x
               grind)
            | exact resolve b6e86 b6e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e75
          have b6e498 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e497
          have b6e499 : (σ x) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b6e498
               have r₂ := b6e86
               grind)
            | exact resolve b6e498 b6e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e86 b6e498
          have b6e500 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e499
               have i₂ := b6e88
               grind)
            | exact superpose b6e88 b6e499
            | exact resolve b6e499 b6e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e88 b6e499
          have b6e501 : False := by grind
          exact b6e501
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e22 : y = (M.op y x) := by grind
            have b7e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : (σ y) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e21
              | exact resolve b7e21 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 (τ X0)
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e34 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 x X0 X1 y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e35 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 y X0 X1 x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b7e14 (M.op (M.op X2 X0) X1) X3 X4 x
                 have i₂ := b7e14 X0 X1 x X2
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b7e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b7e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e39 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b7e37 X0 X1 x x X4
                 have i₂ := b7e14 X0 X1 x x
                 grind)
              | exact superpose b7e14 b7e37
              | exact resolve b7e37 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37
            have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e36 X0 X1 X2 X3 x
                 have i₂ := b7e14 X1 X3 x X0
                 grind)
              | exact superpose b7e14 b7e36
              | exact resolve b7e36 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36
            have b7e41 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b7e34 X0 x
                 have i₂ := b7e35 X0 x
                 grind)
              | exact superpose b7e35 b7e34
              | exact resolve b7e34 b7e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34
            have b7e44 : y = (M.op y y) := by
              first
              | (have i₁ := b7e26
                 have i₂ := b7e41 y
                 grind)
              | exact superpose b7e41 b7e26
              | exact resolve b7e26 b7e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e41
            have b7e67 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b7e35 y x
                 have i₂ := b7e44
                 grind)
              | exact superpose b7e44 b7e35
              | exact resolve b7e35 b7e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e35 b7e44
            have b7e91 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e14 X1 X2 x X0
                 have i₂ := b7e39 (M.op X0 X1) X2 x
                 grind)
              | exact superpose b7e39 b7e14
              | exact resolve b7e14 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e102 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e18 y X0
                 have i₂ := b7e67 X0
                 grind)
              | exact superpose b7e67 b7e18
              | (have j0 := b7e18 y X0
                 grind)
              | (have r₁ := b7e18 y X0
                 have r₂ := b7e67 X0
                 grind)
              | exact resolve b7e18 b7e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e67
            have b7e108 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 := by
              intro X0
              first
              | (have j0 := b7e102 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e102
            have b7e122 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k X0 (τ X1))
                 have i₂ := b7e33 X1 X0
                 grind)
              | exact superpose b7e33 b7e15
              | exact resolve b7e15 b7e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e33
            have b7e150 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e17 X1 (M.op (M.op X2 X3) X0)
                 have i₂ := b7e40 X3 X0 X2 X1
                 grind)
              | exact superpose b7e40 b7e17
              | (have j0 := b7e17 X1 (M.op (M.op X2 X3) X0)
                 grind)
              | (have r₁ := b7e17 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                 have r₂ := b7e40 X0 (M.op X2 X0) X2 (M.op X2 X0)
                 grind)
              | exact resolve b7e17 b7e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e155 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e150 X0 X1 X2 X3
                 have i₂ := b7e91 X2 X3 X0
                 grind)
              | exact superpose b7e91 b7e150
              | (have j0 := b7e150 X0 X1 X2 X3
                 grind)
              | (have r₁ := b7e150 X2 X2 X0 X2
                 have r₂ := b7e91 X0 X2 X2
                 grind)
              | (have r₁ := b7e150 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                 have r₂ := b7e91 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                 grind)
              | exact resolve b7e150 b7e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e150
            have b7e158 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
              intro X0 X1 X3
              first
              | (have i₁ := b7e155 X0 X1 x X3
                 have i₂ := b7e91 x X3 X0
                 grind)
              | exact superpose b7e91 b7e155
              | (have j0 := b7e155 X0 X1 x X3
                 grind)
              | (have r₁ := b7e155 x x x (M.op X0 x)
                 have r₂ := b7e91 X0 x x
                 grind)
              | (have r₁ := b7e155 (M.op X0 X1) (M.op X0 X1) x X1
                 have r₂ := b7e91 X0 X1 (M.op X0 X1)
                 grind)
              | exact resolve b7e155 b7e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e91 b7e155
            have b7e459 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have j0 := b7e158 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e158
            have b7e485 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
              intro X0
              first
              | (have i₁ := b7e122 X0 (M.op (σ X0) (σ X0))
                 have i₂ := b7e459 (σ X0)
                 grind)
              | exact superpose b7e459 b7e122
              | exact resolve b7e122 b7e459
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e122 b7e459
            have b7e502 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b7e485 X0
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e485
              | exact resolve b7e485 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e485
            have b7e832 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
              first
              | (have i₁ := b7e108 (τ (M.op (σ y) (σ y)))
                 have i₂ := b7e502 y
                 grind)
              | exact superpose b7e502 b7e108
              | (have j0 := b7e108 (τ (M.op (σ y) (σ y)))
                 grind)
              | exact resolve b7e108 b7e502
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e108 b7e502
            have b7e833 : y = (τ (M.op (σ y) (σ y))) := by grind
            clear b7e832
            have b7e886 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e16 (M.op (σ y) (σ y))
                 have i₂ := b7e833
                 grind)
              | exact superpose b7e833 b7e16
              | exact resolve b7e16 b7e833
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e833
            have b7e941 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e39 (σ y) (σ y) x
                 have i₂ := b7e886
                 grind)
              | exact superpose b7e886 b7e39
              | exact resolve b7e39 b7e886
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e39 b7e886
            have b7e1027 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b7e28
                 have i₂ := b7e941 (σ x)
                 grind)
              | exact superpose b7e941 b7e28
              | (have r₁ := b7e28
                 have r₂ := b7e941 (σ x)
                 grind)
              | exact resolve b7e28 b7e941
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28 b7e941
            have b7e1036 : False := by grind
            exact b7e1036
          · have b8e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b8e22 : y = (M.op y x) := by grind
            have b8e26 : y ≠ (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e31 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 x X0 X1 y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e33 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b8e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b8e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e35 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b8e33 X0 X1 x x X4
                 have i₂ := b8e14 X0 X1 x x
                 grind)
              | exact superpose b8e14 b8e33
              | exact resolve b8e33 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33
            have b8e37 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e31 x X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e31
              | exact resolve b8e31 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e31
            have b8e49 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b8e37 X1
                 have i₂ := b8e37 X0
                 grind)
              | exact superpose b8e37 b8e37
              | exact resolve b8e37 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37
            have b8e85 : ∀ X0 : G, y ≠ (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e26
                 have i₂ := b8e49 x X0
                 grind)
              | (have i₁ := b8e26
                 have i₂ := b8e49 X0 x
                 grind)
              | exact superpose b8e49 b8e26
              | exact resolve b8e26 b8e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e49
            have b8e92 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e35 y x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e35
              | exact resolve b8e35 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e112 : False := by grind
            exact b8e112
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = (M.op y x) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : x ≠ y := by
            first
            | (have i₁ := b9e21
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e21
            | exact resolve b9e21 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b9e30 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b9e29
          have b9e32 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b9e30
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e30
            | exact resolve b9e30 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e30
          have b9e37 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b9e14 (k x y)
               have i₂ := b9e32
               grind)
            | exact superpose b9e32 b9e14
            | exact resolve b9e14 b9e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32
          have b9e38 : x = (k x y) := by
            first
            | (have i₁ := b9e37
               have i₂ := b9e14 x
               grind)
            | exact superpose b9e14 b9e37
            | exact resolve b9e37 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e37
          have b9e51 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b9e52 : x = y ∨ y = (k x y) := by grind
          clear b9e51
          have b9e53 : y = (k x y) := by
            first
            | (have r₁ := b9e52
               have r₂ := b9e25
               grind)
            | exact resolve b9e52 b9e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52
          have b9e54 : x = y := by
            first
            | (have i₁ := b9e53
               have i₂ := b9e38
               grind)
            | exact superpose b9e38 b9e53
            | exact resolve b9e53 b9e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e38 b9e53
          have b9e55 : False := by grind
          exact b9e55
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : x = (M.op y x) := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : x ≠ (M.op x y) := by grind
            have b10e26 : y = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : x ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e25
              | exact resolve b10e25 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e32 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
              first
              | (have i₁ := b10e17 (σ x) (σ y)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e17
              | (have j0 := b10e17 (σ x) (σ y)
                 grind)
              | (have r₁ := b10e17 (σ x) (σ y)
                 have r₂ := b10e24
                 grind)
              | exact resolve b10e17 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e33 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b10e32
            have b10e34 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b10e33
                 have i₂ := b10e20 x y
                 grind)
              | exact superpose b10e20 b10e33
              | exact resolve b10e33 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33
            have b10e35 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 (k x y)
                 have i₂ := b10e34
                 grind)
              | exact superpose b10e34 b10e15
              | exact resolve b10e15 b10e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e34
            have b10e36 : x = (k x y) := by
              first
              | (have i₁ := b10e35
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e35
              | exact resolve b10e35 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e61 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
            have b10e62 : x = y ∨ y = (k x y) := by grind
            clear b10e61
            have b10e65 : y = (k x y) := by
              first
              | (have r₁ := b10e62
                 have r₂ := b10e27
                 grind)
              | exact resolve b10e62 b10e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e62
            have b10e68 : x = y := by
              first
              | (have i₁ := b10e36
                 have i₂ := b10e65
                 grind)
              | exact superpose b10e65 b10e36
              | exact resolve b10e36 b10e65
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36 b10e65
            have b10e70 : False := by grind
            exact b10e70
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y x) := by grind
            have b11e23 : x = (M.op y x) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : x ≠ y := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e22
              | exact resolve b11e22 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e29 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b11e30 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b11e29
            have b11e31 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e30
              | exact resolve b11e30 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 (k x y)
                 have i₂ := b11e31
                 grind)
              | exact superpose b11e31 b11e15
              | exact resolve b11e15 b11e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e31
            have b11e33 : x = (k x y) := by
              first
              | (have i₁ := b11e32
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e32
              | exact resolve b11e32 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e32
            have b11e57 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
            have b11e61 : x = y ∨ y = (k x y) := by grind
            clear b11e57
            have b11e62 : y = (k x y) := by
              first
              | (have r₁ := b11e61
                 have r₂ := b11e27
                 grind)
              | exact resolve b11e61 b11e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e61
            have b11e64 : x = y := by
              first
              | (have i₁ := b11e33
                 have i₂ := b11e62
                 grind)
              | exact superpose b11e62 b11e33
              | exact resolve b11e33 b11e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33 b11e62
            have b11e66 : False := by grind
            exact b11e66
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b12e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e24
              | exact resolve b12e24 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e31 : x ≠ x ∨ y = (k y x) := by
              first
              | (have i₁ := b12e17 y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e17
              | (have j0 := b12e17 y x
                 grind)
              | (have r₁ := b12e17 y x
                 have r₂ := b12e26
                 grind)
              | exact resolve b12e17 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e33 : y = (k y x) := by grind
            clear b12e31
            have b12e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b12e14 (M.op (M.op X2 X0) X1) X3 X4 x
                 have i₂ := b12e14 X0 X1 x X2
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b12e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b12e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b12e40 X0 X1 x x X4
                 have i₂ := b12e14 X0 X1 x x
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e36 X0 X1 X2 X3 x
                 have i₂ := b12e14 X1 X3 x X0
                 grind)
              | exact superpose b12e14 b12e36
              | exact resolve b12e36 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36
            have b12e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
            have b12e92 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b12e42 (σ y) (σ x) x
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e42
              | exact resolve b12e42 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e99 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 X1 X2 x X0
                 have i₂ := b12e42 (M.op X0 X1) X2 x
                 grind)
              | exact superpose b12e42 b12e14
              | exact resolve b12e14 b12e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e187 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op (M.op X2 X3) X0) ∨ (M.op (M.op X2 X3) X0) = (k X1 (M.op (M.op X2 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e18 X3 (M.op (M.op X2 X0) X1)
                 have i₂ := b12e44 X0 X1 X2 X3
                 grind)
              | exact superpose b12e44 b12e18
              | (have j0 := b12e18 X1 X0
                 grind)
              | exact resolve b12e18 b12e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e44
            have b12e197 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 X0) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op (M.op X2 X3) X0) = (k X1 (M.op (M.op X2 X3) X0)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e187 X0 X1 X2 X3
                 have i₂ := b12e99 X2 X3 X0
                 grind)
              | exact superpose b12e99 b12e187
              | (have j0 := b12e187 X0 X1 X2 X3
                 grind)
              | exact resolve b12e187 b12e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e187
            have b12e200 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X3 X0) ∨ (M.op X3 X0) = (k X1 (M.op X3 X0)) := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e197 x X1 X0 X1
                 have i₂ := b12e99 X0 X1 x
                 grind)
              | exact superpose b12e99 b12e197
              | (have j0 := b12e197 X0 X1 x X3
                 grind)
              | exact resolve b12e197 b12e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e99 b12e197
            have b12e342 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b12e63 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e63
            have b12e1249 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e342 x y
                 have i₂ := b12e33
                 grind)
              | exact superpose b12e33 b12e342
              | (have j0 := b12e342 x y
                 grind)
              | exact resolve b12e342 b12e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e342
            have b12e1253 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
            clear b12e1249
            have b12e1263 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b12e1253
                 have r₂ := b12e29
                 grind)
              | exact resolve b12e1253 b12e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29 b12e1253
            have b12e1297 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ y) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b12e200 (σ x) (σ y) x
                 have i₂ := b12e1263
                 grind)
              | exact superpose b12e1263 b12e200
              | (have j0 := b12e200 (σ x) (σ y) X0
                 grind)
              | (have r₁ := b12e200 (σ x) (σ y) x
                 have r₂ := b12e1263
                 grind)
              | exact resolve b12e200 b12e1263
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e200 b12e1263
            have b12e1299 : ∀ X0 : G, (σ y) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ y) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have j0 := b12e1297 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1297
            have b12e1303 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op X0 (σ x)) = (k (σ y) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have i₁ := b12e1299 X0
                 have i₂ := b12e92 X0
                 grind)
              | exact superpose b12e92 b12e1299
              | (have j0 := b12e1299 X0
                 grind)
              | exact resolve b12e1299 b12e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1299
            have b12e1307 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ y) (M.op X0 (σ x))) := by
              intro X0
              first
              | (have j0 := b12e1303 X0
                 grind)
              | (have r₁ := b12e1303 X0
                 have r₂ := b12e27
                 grind)
              | exact resolve b12e1303 b12e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1303
            have b12e1308 : (σ x) = (k (σ y) (σ x)) := by
              first
              | (have i₁ := b12e1307 x
                 have i₂ := b12e92 x
                 grind)
              | exact superpose b12e92 b12e1307
              | exact resolve b12e1307 b12e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e92 b12e1307
            have b12e1309 : (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b12e1308
                 have i₂ := b12e20 y x
                 grind)
              | exact superpose b12e20 b12e1308
              | exact resolve b12e1308 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1308
            have b12e1310 : (σ x) = (σ y) := by
              first
              | (have i₁ := b12e1309
                 have i₂ := b12e33
                 grind)
              | exact superpose b12e33 b12e1309
              | exact resolve b12e1309 b12e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e33 b12e1309
            have b12e1311 : False := by grind
            exact b12e1311
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b13e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              have b13e27 : x ≠ (M.op x y) := by grind
              have b13e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : x ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e27
                | exact resolve b13e27 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e30 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b13e25
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e25
                | exact resolve b13e25 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e32 : (σ y) ≠ (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e22
                | exact resolve b13e22 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e60 : y ≠ y ∨ x = y ∨ x = (k y x) := by
                first
                | (have i₁ := b13e19 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y x
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e63 : x = y ∨ x = (k y x) := by grind
              clear b13e60
              have b13e67 : x = (k y x) := by
                first
                | (have r₁ := b13e63
                   have r₂ := b13e29
                   grind)
                | exact resolve b13e63 b13e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e29 b13e63
              have b13e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
              have b13e303 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e18 (σ X0) (σ X1)
                   have i₂ := b13e72 X1 X0
                   grind)
                | exact superpose b13e72 b13e18
                | (have j0 := b13e18 (σ X0) (σ X1)
                   have j1 := b13e72 X1 X0
                   grind)
                | (have r₁ := b13e18 (σ X1) (σ X1)
                   have r₂ := b13e72 X1 X1
                   grind)
                | (have r₁ := b13e18 (σ X1) (σ X0)
                   have r₂ := b13e72 X0 X1
                   grind)
                | exact resolve b13e18 b13e72
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e72
              have b13e312 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b13e303 X0 X1
                   have j1 := b13e18 (σ X0) (σ X1)
                   grind)
                | (have r₁ := b13e303 X0 X0
                   have r₂ := b13e18 (σ X0) (σ X0)
                   grind)
                | (have r₁ := b13e303 X0 X1
                   have r₂ := b13e18 (σ X0) (σ X1)
                   grind)
                | exact resolve b13e303 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e303
              have b13e316 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e312 X0 X1
                   have i₂ := b13e21 X0 X1
                   grind)
                | exact superpose b13e21 b13e312
                | (have j0 := b13e312 X0 X1
                   grind)
                | exact resolve b13e312 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e312
              have b13e1089 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b13e316 y x
                   have i₂ := b13e67
                   grind)
                | exact superpose b13e67 b13e316
                | (have j0 := b13e316 y x
                   grind)
                | exact resolve b13e316 b13e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e67 b13e316
              have b13e1094 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
              clear b13e1089
              have b13e1109 : (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b13e1094
                   have r₂ := b13e30
                   grind)
                | exact resolve b13e1094 b13e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e1094
              have b13e1117 : False := by grind
              exact b13e1117
            · have b14e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e27 : x ≠ (M.op x y) := by grind
              have b14e28 : y ≠ (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b14e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e15 (M.op (M.op X2 X0) X1) X3 X4 x
                   have i₂ := b14e15 X0 X1 x X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X3 X0) X1) X4 x
                   have i₂ := b14e15 X0 X1 (M.op x X2) X3
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b14e38 X0 X1 x x X4
                   have i₂ := b14e15 X0 X1 x x
                   grind)
                | exact superpose b14e15 b14e38
                | exact resolve b14e38 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e37 X0 X1 X2 X3 x
                   have i₂ := b14e15 X1 X3 x X0
                   grind)
                | exact superpose b14e15 b14e37
                | exact resolve b14e37 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37
              have b14e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e70 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X2 x X0
                   have i₂ := b14e40 (M.op X0 X1) X2 x
                   grind)
                | exact superpose b14e40 b14e15
                | exact resolve b14e15 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e71 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e19 (M.op X0 X1) x
                   have i₂ := b14e40 X0 X1 x
                   grind)
                | exact superpose b14e40 b14e19
                | (have j0 := b14e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b14e19 (M.op X0 X1) x
                   have r₂ := b14e40 X0 X1 x
                   grind)
                | exact resolve b14e19 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e76 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b14e71 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e71
              have b14e144 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e18 X1 (M.op (M.op X2 X3) X0)
                   have i₂ := b14e41 X3 X0 X2 X1
                   grind)
                | exact superpose b14e41 b14e18
                | (have j0 := b14e18 X1 (M.op (M.op X2 X3) X0)
                   grind)
                | (have r₁ := b14e18 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                   have r₂ := b14e41 X0 (M.op X2 X0) X2 (M.op X2 X0)
                   grind)
                | exact resolve b14e18 b14e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41
              have b14e151 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e144 X0 X1 X2 X3
                   have i₂ := b14e70 X2 X3 X0
                   grind)
                | exact superpose b14e70 b14e144
                | (have j0 := b14e144 X0 X1 X2 X3
                   grind)
                | (have r₁ := b14e144 X2 X2 X0 X2
                   have r₂ := b14e70 X0 X2 X2
                   grind)
                | (have r₁ := b14e144 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                   have r₂ := b14e70 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                   grind)
                | exact resolve b14e144 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e144
              have b14e154 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
                intro X0 X1 X3
                first
                | (have i₁ := b14e151 X0 X1 x X3
                   have i₂ := b14e70 x X3 X0
                   grind)
                | exact superpose b14e70 b14e151
                | (have j0 := b14e151 X0 X1 x X3
                   grind)
                | (have r₁ := b14e151 x x x (M.op X0 x)
                   have r₂ := b14e70 X0 x x
                   grind)
                | (have r₁ := b14e151 (M.op X0 X1) (M.op X0 X1) x X1
                   have r₂ := b14e70 X0 X1 (M.op X0 X1)
                   grind)
                | exact resolve b14e151 b14e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e70 b14e151
              have b14e261 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e60 x y
                   grind)
                | exact superpose b14e60 b14e22
                | (have j1 := b14e60 x y
                   grind)
                | exact resolve b14e22 b14e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e60
              have b14e475 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have j0 := b14e154 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e154
              have b14e504 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b14e33 X0 (M.op (τ X0) (τ X0))
                   have i₂ := b14e475 (τ X0)
                   grind)
                | exact superpose b14e475 b14e33
                | exact resolve b14e33 b14e475
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e33 b14e475
              have b14e520 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b14e504 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e504
                | exact resolve b14e504 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e504
              have b14e586 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b14e76 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   have i₂ := b14e520 (M.op X0 X1)
                   grind)
                | exact superpose b14e520 b14e76
                | (have j0 := b14e76 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b14e76 b14e520
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e76 b14e520
              have b14e598 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b14e586 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e586
              have b14e1178 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e261
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e261
                | (have j1 := b14e20 (σ y) (σ x)
                   grind)
                | exact resolve b14e261 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e261
              have b14e1179 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b14e1178
              have b14e1180 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b14e1179
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e1179 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1179
              have b14e1181 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b14e1180
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e1180 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1180
              have b14e21580 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b14e598 X0 X1
                   grind)
                | exact superpose b14e598 b14e16
                | exact resolve b14e16 b14e598
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e598
              have b14e30645 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e21580 (σ x) (σ y)
                   have i₂ := b14e1181
                   grind)
                | exact superpose b14e1181 b14e21580
                | exact resolve b14e21580 b14e1181
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1181 b14e21580
              have b14e30706 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e30645
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e30645
                | exact resolve b14e30645 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30645
              have b14e31405 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e18 (σ y) (σ x)
                   have i₂ := b14e30706
                   grind)
                | exact superpose b14e30706 b14e18
                | (have j0 := b14e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b14e18 (σ y) (σ x)
                   have r₂ := b14e30706
                   grind)
                | (have r₁ := b14e18 y y
                   have r₂ := b14e30706
                   grind)
                | exact resolve b14e18 b14e30706
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30706
              have b14e31435 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) := by grind
              clear b14e31405
              have b14e31447 : (σ y) = (σ (k y x)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e31435
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e31435
                | exact resolve b14e31435 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31435
              have b14e32067 : (k y x) = (τ (σ y)) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e16 (k y x)
                   have i₂ := b14e31447
                   grind)
                | exact superpose b14e31447 b14e16
                | exact resolve b14e16 b14e31447
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e31447
              have b14e32137 : y = (k y x) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e32067
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e32067
                | exact resolve b14e32067 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32067
              have b14e32269 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b14e20 y x
                   have i₂ := b14e32137
                   grind)
                | exact superpose b14e32137 b14e20
                | (have j0 := b14e20 y x
                   grind)
                | exact resolve b14e20 b14e32137
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32137
              have b14e32288 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by grind
              clear b14e32269
              have b14e32290 : x = (M.op x y) ∨ y = (M.op y y) := by
                first
                | (have r₁ := b14e32288
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e32288 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32288
              have b14e32292 : y = (M.op y y) := by
                first
                | (have r₁ := b14e32290
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e32290 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32290
              have b14e32893 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e40 y y x
                   have i₂ := b14e32292
                   grind)
                | exact superpose b14e32292 b14e40
                | exact resolve b14e40 b14e32292
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40 b14e32292
              have b14e33682 : y ≠ y := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e32893 x
                   grind)
                | exact superpose b14e32893 b14e28
                | (have r₁ := b14e28
                   have r₂ := b14e32893 x
                   grind)
                | exact resolve b14e28 b14e32893
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e32893
              have b14e33691 : False := by grind
              exact b14e33691
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b15e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e23 : x = (M.op y x) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X1 (τ X0)
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e14 x X0 X1 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b15e14 (M.op (M.op X2 X0) X1) X3 X4 x
                 have i₂ := b15e14 X0 X1 x X2
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e37 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b15e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b15e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e39 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b15e37 X0 X1 x x X4
                 have i₂ := b15e14 X0 X1 x x
                 grind)
              | exact superpose b15e14 b15e37
              | exact resolve b15e37 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37
            have b15e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e36 X0 X1 X2 X3 x
                 have i₂ := b15e14 X1 X3 x X0
                 grind)
              | exact superpose b15e14 b15e36
              | exact resolve b15e36 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36
            have b15e41 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b15e34 y x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e34
              | exact resolve b15e34 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e64 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e18 x X0
                 have i₂ := b15e41 X0
                 grind)
              | exact superpose b15e41 b15e18
              | (have j0 := b15e18 x X0
                 grind)
              | (have r₁ := b15e18 x X0
                 have r₂ := b15e41 X0
                 grind)
              | exact resolve b15e18 b15e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e41
            have b15e69 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
              intro X0
              first
              | (have j0 := b15e64 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e64
            have b15e116 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 X1 X2 x X0
                 have i₂ := b15e39 (M.op X0 X1) X2 x
                 grind)
              | exact superpose b15e39 b15e14
              | exact resolve b15e14 b15e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e145 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e15 (k X0 (τ X1))
                 have i₂ := b15e33 X1 X0
                 grind)
              | exact superpose b15e33 b15e15
              | exact resolve b15e15 b15e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e33
            have b15e175 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e17 X1 (M.op (M.op X2 X3) X0)
                 have i₂ := b15e40 X3 X0 X2 X1
                 grind)
              | exact superpose b15e40 b15e17
              | (have j0 := b15e17 X1 (M.op (M.op X2 X3) X0)
                 grind)
              | (have r₁ := b15e17 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                 have r₂ := b15e40 X0 (M.op X2 X0) X2 (M.op X2 X0)
                 grind)
              | exact resolve b15e17 b15e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e40
            have b15e181 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b15e175 X0 X1 X2 X3
                 have i₂ := b15e116 X2 X3 X0
                 grind)
              | exact superpose b15e116 b15e175
              | (have j0 := b15e175 X0 X1 X2 X3
                 grind)
              | (have r₁ := b15e175 X2 X2 X0 X2
                 have r₂ := b15e116 X0 X2 X2
                 grind)
              | (have r₁ := b15e175 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                 have r₂ := b15e116 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                 grind)
              | exact resolve b15e175 b15e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e175
            have b15e185 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
              intro X0 X1 X3
              first
              | (have i₁ := b15e181 X0 X1 x X3
                 have i₂ := b15e116 x X3 X0
                 grind)
              | exact superpose b15e116 b15e181
              | (have j0 := b15e181 X0 X1 x X3
                 grind)
              | (have r₁ := b15e181 x x x (M.op X0 x)
                 have r₂ := b15e116 X0 x x
                 grind)
              | (have r₁ := b15e181 (M.op X0 X1) (M.op X0 X1) x X1
                 have r₂ := b15e116 X0 X1 (M.op X0 X1)
                 grind)
              | exact resolve b15e181 b15e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e116 b15e181
            have b15e549 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have j0 := b15e185 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e185
            have b15e581 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
              intro X0
              first
              | (have i₁ := b15e145 X0 (M.op (σ X0) (σ X0))
                 have i₂ := b15e549 (σ X0)
                 grind)
              | exact superpose b15e549 b15e145
              | exact resolve b15e145 b15e549
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e145 b15e549
            have b15e598 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e581 X0
                 have i₂ := b15e15 X0
                 grind)
              | exact superpose b15e15 b15e581
              | exact resolve b15e581 b15e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e581
            have b15e951 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
              first
              | (have i₁ := b15e69 (τ (M.op (σ x) (σ x)))
                 have i₂ := b15e598 x
                 grind)
              | exact superpose b15e598 b15e69
              | (have j0 := b15e69 (τ (M.op (σ x) (σ x)))
                 grind)
              | exact resolve b15e69 b15e598
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e69 b15e598
            have b15e952 : x = (τ (M.op (σ x) (σ x))) := by grind
            clear b15e951
            have b15e1009 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e16 (M.op (σ x) (σ x))
                 have i₂ := b15e952
                 grind)
              | exact superpose b15e952 b15e16
              | exact resolve b15e16 b15e952
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e952
            have b15e1065 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e39 (σ x) (σ x) x
                 have i₂ := b15e1009
                 grind)
              | exact superpose b15e1009 b15e39
              | exact resolve b15e39 b15e1009
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e39 b15e1009
            have b15e1153 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b15e25
                 have i₂ := b15e1065 (σ y)
                 grind)
              | exact superpose b15e1065 b15e25
              | (have r₁ := b15e25
                 have r₂ := b15e1065 (σ y)
                 grind)
              | exact resolve b15e25 b15e1065
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e1065
            have b15e1165 : False := by grind
            exact b15e1165
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b16e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e24 : x = (M.op y x) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e27 : x ≠ (M.op x y) := by grind
              have b16e28 : y = (M.op x y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : x ≠ y := by
                first
                | (have i₁ := b16e27
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e27
                | exact resolve b16e27 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e54 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
              have b16e60 : x = y ∨ y = (k x y) := by grind
              clear b16e54
              have b16e62 : y = (k x y) := by
                first
                | (have r₁ := b16e60
                   have r₂ := b16e29
                   grind)
                | exact resolve b16e60 b16e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e29 b16e60
              have b16e65 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 X0
                   have i₂ := b16e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b16e20 b16e21
                | (have j1 := b16e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b16e21 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e250 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b16e65 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e65
              have b16e1201 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b16e250 y x
                   have i₂ := b16e62
                   grind)
                | exact superpose b16e62 b16e250
                | (have j0 := b16e250 y x
                   grind)
                | exact resolve b16e250 b16e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e62 b16e250
              have b16e1220 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
              clear b16e1201
              have b16e1233 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have r₁ := b16e1220
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e1220 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e1220
              have b16e1239 : False := by grind
              exact b16e1239
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e24 : x = (M.op y x) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b17e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e15 (M.op (M.op X2 X0) X1) X3 X4 x
                   have i₂ := b17e15 X0 X1 x X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b17e15 X2 (M.op (M.op X3 X0) X1) X4 x
                   have i₂ := b17e15 X0 X1 (M.op x X2) X3
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e37 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b17e35 X0 X1 x x X4
                   have i₂ := b17e15 X0 X1 x x
                   grind)
                | exact superpose b17e15 b17e35
                | exact resolve b17e35 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e34 X0 X1 X2 X3 x
                   have i₂ := b17e15 X1 X3 x X0
                   grind)
                | exact superpose b17e15 b17e34
                | exact resolve b17e34 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e34
              have b17e57 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b17e37 y x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e37
                | exact resolve b17e37 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e62 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 X1 X2 x X0
                   have i₂ := b17e37 (M.op X0 X1) X2 x
                   grind)
                | exact superpose b17e37 b17e15
                | exact resolve b17e15 b17e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e76 : ∀ X0 : G, x ≠ x ∨ x = X0 ∨ (k x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b17e19 x X0
                   have i₂ := b17e57 X0
                   grind)
                | exact superpose b17e57 b17e19
                | (have j0 := b17e19 x X0
                   grind)
                | (have r₁ := b17e19 x X0
                   have r₂ := b17e57 X0
                   grind)
                | exact resolve b17e19 b17e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e57
              have b17e81 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
                intro X0
                first
                | (have j0 := b17e76 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e76
              have b17e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e16 (k X0 (τ X1))
                   have i₂ := b17e32 X1 X0
                   grind)
                | exact superpose b17e32 b17e16
                | exact resolve b17e16 b17e32
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e32
              have b17e109 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e18 X1 (M.op (M.op X2 X3) X0)
                   have i₂ := b17e38 X3 X0 X2 X1
                   grind)
                | exact superpose b17e38 b17e18
                | (have j0 := b17e18 X1 (M.op (M.op X2 X3) X0)
                   grind)
                | (have r₁ := b17e18 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                   have r₂ := b17e38 X0 (M.op X2 X0) X2 (M.op X2 X0)
                   grind)
                | exact resolve b17e18 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e38
              have b17e114 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e109 X0 X1 X2 X3
                   have i₂ := b17e62 X2 X3 X0
                   grind)
                | exact superpose b17e62 b17e109
                | (have j0 := b17e109 X0 X1 X2 X3
                   grind)
                | (have r₁ := b17e109 X2 X2 X0 X2
                   have r₂ := b17e62 X0 X2 X2
                   grind)
                | (have r₁ := b17e109 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                   have r₂ := b17e62 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                   grind)
                | exact resolve b17e109 b17e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e109
              have b17e117 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
                intro X0 X1 X3
                first
                | (have i₁ := b17e114 X0 X1 x X3
                   have i₂ := b17e62 x X3 X0
                   grind)
                | exact superpose b17e62 b17e114
                | (have j0 := b17e114 X0 X1 x X3
                   grind)
                | (have r₁ := b17e114 x x x (M.op X0 x)
                   have r₂ := b17e62 X0 x x
                   grind)
                | (have r₁ := b17e114 (M.op X0 X1) (M.op X0 X1) x X1
                   have r₂ := b17e62 X0 X1 (M.op X0 X1)
                   grind)
                | exact resolve b17e114 b17e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e62 b17e114
              have b17e403 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have j0 := b17e117 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e117
              have b17e426 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                first
                | (have i₁ := b17e89 X0 (M.op (σ X0) (σ X0))
                   have i₂ := b17e403 (σ X0)
                   grind)
                | exact superpose b17e403 b17e89
                | exact resolve b17e89 b17e403
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e89 b17e403
              have b17e444 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e426 X0
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e426
                | exact resolve b17e426 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e426
              have b17e805 : x = (τ (M.op (σ x) (σ x))) ∨ x = (τ (M.op (σ x) (σ x))) := by
                first
                | (have i₁ := b17e81 (τ (M.op (σ x) (σ x)))
                   have i₂ := b17e444 x
                   grind)
                | exact superpose b17e444 b17e81
                | (have j0 := b17e81 (τ (M.op (σ x) (σ x)))
                   grind)
                | exact resolve b17e81 b17e444
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e81 b17e444
              have b17e806 : x = (τ (M.op (σ x) (σ x))) := by grind
              clear b17e805
              have b17e867 : (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b17e17 (M.op (σ x) (σ x))
                   have i₂ := b17e806
                   grind)
                | exact superpose b17e806 b17e17
                | exact resolve b17e17 b17e806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e806
              have b17e929 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
                intro X0
                first
                | (have i₁ := b17e37 (σ x) (σ x) x
                   have i₂ := b17e867
                   grind)
                | exact superpose b17e867 b17e37
                | exact resolve b17e37 b17e867
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37 b17e867
              have b17e1012 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e929 (σ y)
                   grind)
                | exact superpose b17e929 b17e26
                | (have r₁ := b17e26
                   have r₂ := b17e929 (σ y)
                   grind)
                | exact resolve b17e26 b17e929
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e929
              have b17e1019 : False := by grind
              exact b17e1019
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ (M.op y x) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b18e28 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b18e27
          have b18e30 : (σ x) = (σ (k x y)) := by
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
          have b18e35 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e30
               grind)
            | exact superpose b18e30 b18e14
            | exact resolve b18e14 b18e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e36 : x = (k x y) := by
            first
            | (have i₁ := b18e35
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e35
            | exact resolve b18e35 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e62 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e36
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e36 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e66 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b18e62
          have b18e70 : y = (M.op y x) := by
            first
            | (have r₁ := b18e66
               have r₂ := b18e22
               grind)
            | exact resolve b18e66 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e66
          have b18e73 : False := by grind
          exact b18e73
        · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ (M.op y x) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b19e31 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b19e30
            have b19e32 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e31
              | exact resolve b19e31 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e37 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e32
                 grind)
              | exact superpose b19e32 b19e15
              | exact resolve b19e15 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e38 : x = (k x y) := by
              first
              | (have i₁ := b19e37
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e37
              | exact resolve b19e37 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37
            have b19e56 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e38
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e38
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e38 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e60 : x = (M.op y x) ∨ y = (M.op y x) := by grind
            clear b19e56
            have b19e64 : y = (M.op y x) := by
              first
              | (have r₁ := b19e60
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e60 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e60
            have b19e67 : False := by grind
            exact b19e67
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y x) := by grind
            have b20e23 : x ≠ (M.op y x) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b20e27
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
            have b20e74 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
            have b20e76 : x = (M.op y x) ∨ y = (M.op y x) := by grind
            clear b20e74
            have b20e79 : y = (M.op y x) := by
              first
              | (have r₁ := b20e76
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e76 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e76
            have b20e82 : False := by grind
            exact b20e82
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op y x) := by grind
            have b21e23 : x ≠ (M.op y x) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b21e24
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e24
              | exact resolve b21e24 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e51 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b21e54 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b21e51
            have b21e55 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e54
                 have r₂ := b21e27
                 grind)
              | exact resolve b21e54 b21e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e27 b21e54
            have b21e56 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e55
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e55
              | exact resolve b21e55 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e55
            have b21e59 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e56
                 grind)
              | exact superpose b21e56 b21e15
              | exact resolve b21e15 b21e56
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e56
            have b21e60 : y = (k x y) := by
              first
              | (have i₁ := b21e59
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e59
              | exact resolve b21e59 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e59
            have b21e73 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e60
                 grind)
              | exact superpose b21e60 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e60
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e60
            have b21e74 : y = (M.op y x) ∨ x = (M.op y x) := by grind
            clear b21e73
            have b21e76 : x = (M.op y x) := by
              first
              | (have r₁ := b21e74
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e74 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e74
            have b21e78 : False := by grind
            exact b21e78
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : y ≠ (M.op y x) := by grind
              have b22e24 : x ≠ (M.op y x) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b22e25
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e25
                | exact resolve b22e25 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e50 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
              have b22e54 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b22e50
              have b22e56 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e54
                   have r₂ := b22e30
                   grind)
                | exact resolve b22e54 b22e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e30 b22e54
              have b22e58 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e56
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e56
                | exact resolve b22e56 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e56
              have b22e68 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e58
                   grind)
                | exact superpose b22e58 b22e16
                | exact resolve b22e16 b22e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e58
              have b22e69 : y = (k x y) := by
                first
                | (have i₁ := b22e68
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e68
                | exact resolve b22e68 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e68
              have b22e89 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e69
                   grind)
                | exact superpose b22e69 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e69
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e69
              have b22e90 : y = (M.op y x) ∨ x = (M.op y x) := by grind
              clear b22e89
              have b22e92 : x = (M.op y x) := by
                first
                | (have r₁ := b22e90
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e90 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e90
              have b22e94 : False := by grind
              exact b22e94
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op y x) := by grind
              have b23e24 : x ≠ (M.op y x) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b23e25
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e25
                | exact resolve b23e25 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e48 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
              have b23e52 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b23e48
              have b23e54 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e52
                   have r₂ := b23e29
                   grind)
                | exact resolve b23e52 b23e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29 b23e52
              have b23e56 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e54
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e54
                | exact resolve b23e54 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e54
              have b23e59 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e56
                   grind)
                | exact superpose b23e56 b23e16
                | exact resolve b23e16 b23e56
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e56
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
              have b23e69 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
              have b23e70 : y = (M.op y x) ∨ x = (M.op y x) := by grind
              clear b23e69
              have b23e72 : x = (M.op y x) := by
                first
                | (have r₁ := b23e70
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e70 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e70
              have b23e74 : False := by grind
              exact b23e74
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b24e23 : x ≠ (M.op y x) := by grind
            have b24e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e32 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 y X0 X1 x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b24e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b24e34 X0 X1 x x X4
                 have i₂ := b24e14 X0 X1 x x
                 grind)
              | exact superpose b24e14 b24e34
              | exact resolve b24e34 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e38 : ∀ X0 : G, (M.op y y) = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b24e32 y X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e32
              | exact resolve b24e32 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32
            have b24e50 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) := by
              intro X0 X1
              first
              | (have i₁ := b24e38 X1
                 have i₂ := b24e38 X0
                 grind)
              | exact superpose b24e38 b24e38
              | exact resolve b24e38 b24e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e38
            have b24e87 : ∀ X0 : G, x ≠ (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b24e23
                 have i₂ := b24e50 y X0
                 grind)
              | (have i₁ := b24e23
                 have i₂ := b24e50 X0 y
                 grind)
              | exact superpose b24e50 b24e23
              | exact resolve b24e23 b24e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e50
            have b24e93 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b24e36 x y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e36
              | exact resolve b24e36 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36
            have b24e113 : False := by grind
            exact b24e113
          · rcases eq_or_ne (M.op x y) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
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
              have b25e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
              have b25e35 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e15 (M.op (M.op X2 X0) X1) X3 X4 x
                   have i₂ := b25e15 X0 X1 x X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X3 X0) X1) X4 x
                   have i₂ := b25e15 X0 X1 (M.op x X2) X3
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b25e36 X0 X1 x x X4
                   have i₂ := b25e15 X0 X1 x x
                   grind)
                | exact superpose b25e15 b25e36
                | exact resolve b25e36 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36
              have b25e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e35 X0 X1 X2 X3 x
                   have i₂ := b25e15 X1 X3 x X0
                   grind)
                | exact superpose b25e15 b25e35
                | exact resolve b25e35 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e58 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b25e38 x y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e38
                | exact resolve b25e38 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e63 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 X2 x X0
                   have i₂ := b25e38 (M.op X0 X1) X2 x
                   grind)
                | exact superpose b25e38 b25e15
                | exact resolve b25e15 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e77 : ∀ X0 : G, y ≠ y ∨ y = X0 ∨ (k y X0) = X0 := by
                intro X0
                first
                | (have i₁ := b25e19 y X0
                   have i₂ := b25e58 X0
                   grind)
                | exact superpose b25e58 b25e19
                | (have j0 := b25e19 y X0
                   grind)
                | (have r₁ := b25e19 y X0
                   have r₂ := b25e58 X0
                   grind)
                | exact resolve b25e19 b25e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e58
              have b25e82 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 := by
                intro X0
                first
                | (have j0 := b25e77 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e77
              have b25e90 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e16 (k X0 (τ X1))
                   have i₂ := b25e33 X1 X0
                   grind)
                | exact superpose b25e33 b25e16
                | exact resolve b25e16 b25e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e33
              have b25e110 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e18 X1 (M.op (M.op X2 X3) X0)
                   have i₂ := b25e39 X3 X0 X2 X1
                   grind)
                | exact superpose b25e39 b25e18
                | (have j0 := b25e18 X1 (M.op (M.op X2 X3) X0)
                   grind)
                | (have r₁ := b25e18 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                   have r₂ := b25e39 X0 (M.op X2 X0) X2 (M.op X2 X0)
                   grind)
                | exact resolve b25e18 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39
              have b25e115 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e110 X0 X1 X2 X3
                   have i₂ := b25e63 X2 X3 X0
                   grind)
                | exact superpose b25e63 b25e110
                | (have j0 := b25e110 X0 X1 X2 X3
                   grind)
                | (have r₁ := b25e110 X2 X2 X0 X2
                   have r₂ := b25e63 X0 X2 X2
                   grind)
                | (have r₁ := b25e110 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                   have r₂ := b25e63 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                   grind)
                | exact resolve b25e110 b25e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e110
              have b25e118 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
                intro X0 X1 X3
                first
                | (have i₁ := b25e115 X0 X1 x X3
                   have i₂ := b25e63 x X3 X0
                   grind)
                | exact superpose b25e63 b25e115
                | (have j0 := b25e115 X0 X1 x X3
                   grind)
                | (have r₁ := b25e115 x x x (M.op X0 x)
                   have r₂ := b25e63 X0 x x
                   grind)
                | (have r₁ := b25e115 (M.op X0 X1) (M.op X0 X1) x X1
                   have r₂ := b25e63 X0 X1 (M.op X0 X1)
                   grind)
                | exact resolve b25e115 b25e63
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e63 b25e115
              have b25e403 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have j0 := b25e118 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e118
              have b25e426 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                first
                | (have i₁ := b25e90 X0 (M.op (σ X0) (σ X0))
                   have i₂ := b25e403 (σ X0)
                   grind)
                | exact superpose b25e403 b25e90
                | exact resolve b25e90 b25e403
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e90 b25e403
              have b25e444 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b25e426 X0
                   have i₂ := b25e16 X0
                   grind)
                | exact superpose b25e16 b25e426
                | exact resolve b25e426 b25e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e426
              have b25e805 : y = (τ (M.op (σ y) (σ y))) ∨ y = (τ (M.op (σ y) (σ y))) := by
                first
                | (have i₁ := b25e82 (τ (M.op (σ y) (σ y)))
                   have i₂ := b25e444 y
                   grind)
                | exact superpose b25e444 b25e82
                | (have j0 := b25e82 (τ (M.op (σ y) (σ y)))
                   grind)
                | exact resolve b25e82 b25e444
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e82 b25e444
              have b25e806 : y = (τ (M.op (σ y) (σ y))) := by grind
              clear b25e805
              have b25e867 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e17 (M.op (σ y) (σ y))
                   have i₂ := b25e806
                   grind)
                | exact superpose b25e806 b25e17
                | exact resolve b25e17 b25e806
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e806
              have b25e929 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e38 (σ y) (σ y) x
                   have i₂ := b25e867
                   grind)
                | exact superpose b25e867 b25e38
                | exact resolve b25e38 b25e867
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38 b25e867
              have b25e1013 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b25e30
                   have i₂ := b25e929 (σ x)
                   grind)
                | exact superpose b25e929 b25e30
                | (have r₁ := b25e30
                   have r₂ := b25e929 (σ x)
                   grind)
                | exact resolve b25e30 b25e929
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30 b25e929
              have b25e1018 : False := by grind
              exact b25e1018
            · have b26e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e24 : x ≠ (M.op y x) := by grind
              have b26e27 : x ≠ (M.op x y) := by grind
              have b26e28 : y ≠ (M.op x y) := by grind
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
              have b26e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X3 X0) X1) X4 x
                   have i₂ := b26e15 X0 X1 (M.op x X2) X3
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e34 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b26e32 X0 X1 x x X4
                   have i₂ := b26e15 X0 X1 x x
                   grind)
                | exact superpose b26e15 b26e32
                | exact resolve b26e32 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e32
              have b26e39 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X1 X2 x X0
                   have i₂ := b26e34 (M.op X0 X1) X2 x
                   grind)
                | exact superpose b26e34 b26e15
                | exact resolve b26e15 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 (M.op X0 X1) x
                   have i₂ := b26e34 X0 X1 x
                   grind)
                | exact superpose b26e34 b26e19
                | (have j0 := b26e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e19 (M.op X0 X1) x
                   have r₂ := b26e34 X0 X1 x
                   grind)
                | exact resolve b26e19 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e46 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e45 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e45
              have b26e57 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (k X1 (M.op X2 X0)) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e18 X1 (M.op X2 X0)
                   have i₂ := b26e39 X2 X0 X1
                   grind)
                | exact superpose b26e39 b26e18
                | (have j0 := b26e18 X1 (M.op X2 X0)
                   grind)
                | (have r₁ := b26e18 X2 (M.op X2 X2)
                   have r₂ := b26e39 X2 X2 X2
                   grind)
                | exact resolve b26e18 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e39
              have b26e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
              have b26e147 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e62 x y
                   grind)
                | exact superpose b26e62 b26e22
                | (have j1 := b26e62 x y
                   grind)
                | exact resolve b26e22 b26e62
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e62
              have b26e217 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have j0 := b26e57 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e57
              have b26e254 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b26e29 X0 (M.op (τ X0) (τ X0))
                   have i₂ := b26e217 (τ X0)
                   grind)
                | exact superpose b26e217 b26e29
                | exact resolve b26e29 b26e217
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29 b26e217
              have b26e260 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e254 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e254
                | exact resolve b26e254 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e254
              have b26e303 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e46 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   have i₂ := b26e260 (M.op X0 X1)
                   grind)
                | exact superpose b26e260 b26e46
                | (have j0 := b26e46 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b26e46 b26e260
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46 b26e260
              have b26e309 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b26e303 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e303
              have b26e740 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e147
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e147
                | (have j1 := b26e20 (σ y) (σ x)
                   grind)
                | exact resolve b26e147 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e147
              have b26e741 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b26e740
              have b26e742 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b26e741
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e741 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e741
              have b26e743 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e742
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e742 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e742
              have b26e1725 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b26e309 X0 X1
                   grind)
                | exact superpose b26e309 b26e16
                | exact resolve b26e16 b26e309
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e309
              have b26e2027 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e1725 X0 X1
                   grind)
                | exact superpose b26e1725 b26e34
                | exact resolve b26e34 b26e1725
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e1725
              have b26e2239 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e2027 (σ x) (σ y) x
                   have i₂ := b26e743
                   grind)
                | exact superpose b26e743 b26e2027
                | exact resolve b26e2027 b26e743
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e743
              have b26e2242 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e2239 X0
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e2239
                | exact resolve b26e2239 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2239
              have b26e2487 : ∀ X0 X1 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ y = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b26e2027 (σ x) (σ y) x
                   have i₂ := b26e2242 X0
                   grind)
                | exact superpose b26e2242 b26e2027
                | (have j1 := b26e2242 X1
                   grind)
                | exact resolve b26e2027 b26e2242
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2027 b26e2242
              have b26e2492 : ∀ X0 X1 : G, x = (M.op X0 x) ∨ y = (M.op X1 y) := by
                intro X0 X1
                first
                | (have i₁ := b26e2487 X0 X1
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e2487
                | (have j0 := b26e2487 X0 X1
                   grind)
                | exact resolve b26e2487 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2487
              have b26e2593 : ∀ X0 : G, y ≠ y ∨ x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b26e28
                   have i₂ := b26e2492 X0 x
                   grind)
                | exact superpose b26e2492 b26e28
                | (have j1 := b26e2492 X0 x
                   grind)
                | (have r₁ := b26e28
                   have r₂ := b26e2492 X0 x
                   grind)
                | exact resolve b26e28 b26e2492
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2492
              have b26e2595 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have j0 := b26e2593 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2593
              have b26e2807 : x ≠ x := by
                first
                | (have i₁ := b26e24
                   have i₂ := b26e2595 y
                   grind)
                | exact superpose b26e2595 b26e24
                | (have r₁ := b26e24
                   have r₂ := b26e2595 y
                   grind)
                | exact resolve b26e24 b26e2595
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2595
              have b26e2809 : False := by grind
              exact b26e2809

/-- `Equation3735`: `x ◇ y = (x ◇ z) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3735 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3735 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3735.models_iff G M).mp hM
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
        have b1e46 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e48 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e46
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e23
             grind)
          | exact resolve b1e48 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e50
          | exact resolve b1e50 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e50
        have b1e52 : False := by grind
        exact b1e52
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
        have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e415 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e49 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e17466 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e415 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e415
          | (have j0 := b2e415 x y
             grind)
          | exact resolve b2e415 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e415
        have b2e17474 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e17466
        have b2e17483 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e17474
             have r₂ := b2e22
             grind)
          | exact resolve b2e17474 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17474
        have b2e17492 : False := by grind
        exact b2e17492
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
        have b3e45 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e47 : x = y ∨ y = (k x y) := by grind
        clear b3e45
        have b3e48 : y = (k x y) := by
          first
          | (have r₁ := b3e47
             have r₂ := b3e23
             grind)
          | exact resolve b3e47 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e47
        have b3e51 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e29
          | exact resolve b3e29 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e48
        have b3e52 : False := by grind
        exact b3e52
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
          have b5e42 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e45 : x = y ∨ y = (k x y) := by grind
          clear b5e42
          have b5e46 : y = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e25
               grind)
            | exact resolve b5e45 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e45
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
          have b5e363 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e11461 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e363 x y
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e363
            | (have j0 := b5e363 x y
               grind)
            | exact resolve b5e363 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e363
          have b5e11468 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e11461
          have b5e11473 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e11468
               have r₂ := b5e24
               grind)
            | exact resolve b5e11468 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11468
          have b5e11480 : False := by grind
          exact b5e11480
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
        have b6e49 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e51 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e49
        have b6e54 : y = (M.op x y) := by
          first
          | (have r₁ := b6e51
             have r₂ := b6e21
             grind)
          | exact resolve b6e51 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e57 : False := by grind
        exact b6e57
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
          have b7e39 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e41 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e39
          have b7e42 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e41
               have r₂ := b7e25
               grind)
            | exact resolve b7e41 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e41
          have b7e43 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e42
            | exact resolve b7e42 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e14
            | exact resolve b7e14 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : y = (k x y) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e46
            | exact resolve b7e46 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e57 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e57
          have b7e60 : x = (M.op x y) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e21
               grind)
            | exact resolve b7e58 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e62 : False := by grind
          exact b7e62
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
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e358 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e20
            | (have j1 := b8e44 x y
               grind)
            | exact resolve b8e20 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e388 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e358
               have r₂ := b8e24
               grind)
            | exact resolve b8e358 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e395 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e388
               have r₂ := b8e23
               grind)
            | exact resolve b8e388 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e388
          have b8e398 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e395
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e395
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e395 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e395
          have b8e399 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e398
          have b8e400 : y = (M.op x y) := by
            first
            | (have r₁ := b8e399
               have r₂ := b8e22
               grind)
            | exact resolve b8e399 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399
          have b8e401 : False := by grind
          exact b8e401

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pxy_Equation3744 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e86 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e91 : False := by grind
      exact b0e91
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
          have b4e34 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
            intro X0 X1 X2 X3 X5
            first
            | (have i₁ := b4e13 (M.op X0 X2) X3 (M.op x X1) X5
               have i₂ := b4e13 X0 X1 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e34 X0 x X2 X3 x
               have i₂ := b4e13 X0 X3 x x
               grind)
            | exact superpose b4e13 b4e34
            | exact resolve b4e34 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e45 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 x X1 (M.op x X0) X3
               have i₂ := b4e32 X0 x
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e46 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b4e45 x X1 x
               have i₂ := b4e13 y X1 x x
               grind)
            | exact superpose b4e13 b4e45
            | exact resolve b4e45 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e115 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e39 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e193 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e30 y
               have i₂ := b4e115 (σ y)
               grind)
            | exact superpose b4e115 b4e30
            | exact resolve b4e30 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e115
          have b4e205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e193
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e193
            | exact resolve b4e193 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e193
          have b4e209 : False := by grind
          exact b4e209
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
          have b5e33 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b5e37 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e33 X0 x X2 X3 x
               have i₂ := b5e13 X0 X3 x x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e42 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 x X1 (M.op x X0) X3
               have i₂ := b5e32 X0 x
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e43 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b5e42 x X1 x
               have i₂ := b5e13 y X1 x x
               grind)
            | exact superpose b5e13 b5e42
            | exact resolve b5e42 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e47 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e50 : x = y ∨ y = (k x y) := by grind
          clear b5e47
          have b5e52 : y = (k x y) := by
            first
            | (have r₁ := b5e50
               have r₂ := b5e21
               grind)
            | exact resolve b5e50 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e196 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e55 x y
               grind)
            | exact superpose b5e55 b5e24
            | (have j1 := b5e55 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e55 x y
               grind)
            | exact resolve b5e24 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e206 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b5e196
          have b5e212 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e206
               have r₂ := b5e23
               grind)
            | exact resolve b5e206 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e206
          have b5e222 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e212
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e212
            | exact resolve b5e212 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e212
          have b5e229 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e37 (σ x) (σ y) X0
               have i₂ := b5e222
               grind)
            | exact superpose b5e222 b5e37
            | exact resolve b5e37 b5e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e222
          have b5e402 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e30 y
               have i₂ := b5e229 (σ y)
               grind)
            | exact superpose b5e229 b5e30
            | exact resolve b5e30 b5e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e229
          have b5e423 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e402
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e402
            | exact resolve b5e402 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e402
          have b5e429 : False := by grind
          exact b5e429
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e33 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b7e37 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e33 X0 x X2 X3 x
               have i₂ := b7e13 X0 X3 x x
               grind)
            | exact superpose b7e13 b7e33
            | exact resolve b7e33 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e47 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e51 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e51
            | exact resolve b7e51 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e61 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e52
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e52 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e62 : (σ (M.op x y)) = (σ y) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e63 : (σ (M.op x y)) = (σ y) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e70 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e37 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e126 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b7e30 (M.op x y)
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e30
            | exact resolve b7e30 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e63
          have b7e133 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e126
               have i₂ := b7e13 x y y x
               grind)
            | exact superpose b7e13 b7e126
            | exact resolve b7e126 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e135 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e133
               have i₂ := b7e70 (σ y)
               grind)
            | exact superpose b7e70 b7e133
            | exact resolve b7e133 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e133
          have b7e137 : False := by grind
          exact b7e137
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e114 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e64 x y
               grind)
            | exact superpose b8e64 b8e24
            | (have j1 := b8e64 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e64 x y
               grind)
            | exact resolve b8e24 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e122 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b8e114
          have b8e128 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e122
               have r₂ := b8e23
               grind)
            | exact resolve b8e122 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e221 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e128
               grind)
            | exact superpose b8e128 b8e20
            | exact resolve b8e20 b8e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e270 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e221
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e221
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e221
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e221
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e221 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e221
          have b8e271 : x = (M.op y x) ∨ x = y := by grind
          clear b8e270
          have b8e272 : x = y := by
            first
            | (have r₁ := b8e271
               have r₂ := b8e22
               grind)
            | exact resolve b8e271 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271
          have b8e273 : False := by grind
          exact b8e273
