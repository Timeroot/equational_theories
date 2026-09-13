import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1594`: `x = (y ◇ z) ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_y_pyx_x_pxy_Equation1594 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1594 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1594.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e50 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
      have b0e120 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e50 x
           grind)
        | exact superpose b0e50 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e50 x
           grind)
        | exact resolve b0e22 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e50
      have b0e127 : False := by grind
      exact b0e127
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e33 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b1e12 y X0 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : x = y := by
          first
          | (have i₁ := b1e33 x
             have i₂ := b1e12 x x x
             grind)
          | exact superpose b1e12 b1e33
          | exact resolve b1e33 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e40 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e21
          | exact resolve b1e21 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e41 : False := by grind
        exact b1e41
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e32 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op x (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b2e12 y X0 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : x = y := by
          first
          | (have i₁ := b2e32 x
             have i₂ := b2e12 x x x
             grind)
          | exact superpose b2e12 b2e32
          | exact resolve b2e32 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e37 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e21
          | exact resolve b2e21 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34
        have b2e38 : False := by grind
        exact b2e38
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e36 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e36 x
             have i₂ := b3e12 (σ x) x (σ x)
             grind)
          | exact superpose b3e12 b3e36
          | exact resolve b3e36 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e41 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e13
          | exact resolve b3e13 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e42 : x = y := by
          first
          | (have i₁ := b3e41
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e41
          | exact resolve b3e41 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e54 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e42
             grind)
          | exact superpose b3e42 b3e20
          | exact resolve b3e20 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e56 : False := by grind
        exact b3e56
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 : G, (M.op y (M.op x (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (σ x) X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e29 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X2 X0)) (M.op (M.op X2 (M.op X2 X0)) X3))) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op x X2) (M.op X2 (M.op X2 X0))
               have i₂ := b4e13 X0 x X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e42 (σ X0)
               grind)
            | exact superpose b4e42 b4e19
            | exact resolve b4e19 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e44 X0
               have i₂ := b4e42 X0
               grind)
            | exact superpose b4e42 b4e44
            | exact resolve b4e44 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e44
          have b4e232 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X2 X1) X0)) = (M.op X1 (M.op (M.op X2 (M.op X2 X1)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e29 X1 X2 (M.op (M.op X2 X1) (M.op (M.op X2 X1) X0))
               have i₂ := b4e13 X0 X2 (M.op X2 X1)
               grind)
            | exact superpose b4e13 b4e29
            | exact resolve b4e29 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29
          have b4e311 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 x (M.op X1 X0)
               have i₂ := b4e32 (M.op (M.op X1 X0) X2) x X1 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e401 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e311 x y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e311
            | exact resolve b4e311 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e422 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 (M.op (M.op X1 (σ x)) X0)
               have i₂ := b4e311 (σ x) X1 X0
               grind)
            | exact superpose b4e311 b4e28
            | exact resolve b4e28 b4e311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e424 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 (M.op (M.op X1 x) X0)
               have i₂ := b4e311 x X1 X0
               grind)
            | exact superpose b4e311 b4e27
            | exact resolve b4e27 b4e311
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e311
          have b4e533 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e27 (M.op x (M.op y X0))
               have i₂ := b4e401 X0
               grind)
            | exact superpose b4e401 b4e27
            | exact resolve b4e27 b4e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e538 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x (M.op y X0)) (M.op (M.op x (M.op y X0)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 x (M.op x (M.op y X0))
               have i₂ := b4e401 X0
               grind)
            | exact superpose b4e401 b4e13
            | exact resolve b4e13 b4e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e551 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y X0) (M.op (M.op x (M.op x (M.op y X0))) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e538 X0 X1
               have i₂ := b4e232 X1 (M.op y X0) x
               grind)
            | exact superpose b4e232 b4e538
            | exact resolve b4e538 b4e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e232 b4e538
          have b4e556 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e551 X0 X1
               have i₂ := b4e401 X0
               grind)
            | exact superpose b4e401 b4e551
            | exact resolve b4e551 b4e401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e401 b4e551
          have b4e1250 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e422 X0 (σ x)
               have i₂ := b4e45 x
               grind)
            | exact superpose b4e45 b4e422
            | exact resolve b4e422 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e422
          have b4e1802 : (σ x) = (M.op (σ y) (M.op (M.op y (σ y)) (σ y))) := by
            first
            | (have i₁ := b4e556 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e556
            | exact resolve b4e556 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1807 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (M.op (σ y) (M.op (M.op y (σ y)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e556 (σ y) (M.op (σ x) (M.op (σ x) X0))
               have i₂ := b4e28 X0
               grind)
            | exact superpose b4e28 b4e556
            | exact resolve b4e556 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e556
          have b4e1882 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e1802
               have i₂ := b4e1807 (σ y)
               grind)
            | exact superpose b4e1807 b4e1802
            | exact resolve b4e1802 b4e1807
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1802 b4e1807
          have b4e2573 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e45 (M.op x x)
               have i₂ := b4e1250 (σ (M.op x x))
               grind)
            | exact superpose b4e1250 b4e45
            | exact resolve b4e45 b4e1250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1250
          have b4e2647 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b4e2573
               have i₂ := b4e424 (M.op x x) x
               grind)
            | exact superpose b4e424 b4e2573
            | exact resolve b4e2573 b4e424
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e424 b4e2573
          have b4e2676 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op y x))) := by
            first
            | (have i₁ := b4e2647
               have i₂ := b4e533 x
               grind)
            | exact superpose b4e533 b4e2647
            | exact resolve b4e2647 b4e533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533 b4e2647
          have b4e2694 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e2676
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e2676
            | exact resolve b4e2676 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2676
          have b4e3698 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b4e28 (M.op (σ x) (σ y))
               have i₂ := b4e1882
               grind)
            | exact superpose b4e1882 b4e28
            | exact resolve b4e28 b4e1882
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e1882
          have b4e3755 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e3698
               have i₂ := b4e45 x
               grind)
            | exact superpose b4e45 b4e3698
            | exact resolve b4e3698 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e3698
          have b4e3773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e3755
               have i₂ := b4e2694
               grind)
            | exact superpose b4e2694 b4e3755
            | exact resolve b4e3755 b4e2694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2694 b4e3755
          have b4e3786 : False := by grind
          exact b4e3786
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op y y)) := by
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
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e40 (σ X0)
               grind)
            | exact superpose b5e40 b5e19
            | exact resolve b5e19 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e42 X0
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e42
            | exact resolve b5e42 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e42
          have b5e45 : y ≠ y ∨ (M.op x y) = (M.op x x) ∨ x = (k x y) := by
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
          have b5e49 : (M.op x y) = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e45
          have b5e51 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e79 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e58 X0 X1
               have i₂ := b5e43 X0
               grind)
            | exact superpose b5e43 b5e58
            | (have j0 := b5e58 X0 X1
               grind)
            | exact resolve b5e58 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e198 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 x (M.op X1 X0)
               have i₂ := b5e30 (M.op (M.op X1 X0) X2) x X1 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e432 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X3 X2) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X3 X2) X0) X1 X2
               have i₂ := b5e198 X2 X3 X0
               grind)
            | exact superpose b5e198 b5e13
            | exact resolve b5e13 b5e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e198
          have b5e708 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e79 x y
               grind)
            | exact superpose b5e79 b5e24
            | (have j1 := b5e79 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e79 x y
               grind)
            | exact resolve b5e24 b5e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e727 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b5e708
          have b5e748 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e727
               have i₂ := b5e51
               grind)
            | exact superpose b5e51 b5e727
            | exact resolve b5e727 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51 b5e727
          have b5e7252 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e748
               grind)
            | exact superpose b5e748 b5e23
            | exact resolve b5e23 b5e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e748
          have b5e7295 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e7252
               have r₂ := b5e43 x
               grind)
            | exact resolve b5e7252 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7252
          have b5e7309 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ x))) := by
            intro X0
            first
            | (have i₁ := b5e13 (σ y) X0 (σ x)
               have i₂ := b5e7295
               grind)
            | exact superpose b5e7295 b5e13
            | exact resolve b5e13 b5e7295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7313 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) X0)) = (M.op (M.op X1 (σ x)) (M.op (σ x) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X0 X1 (σ x) (σ y)
               have i₂ := b5e7295
               grind)
            | exact superpose b5e7295 b5e30
            | exact resolve b5e30 b5e7295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e7330 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e432 X1 X0 (σ y) (σ x)
               have i₂ := b5e7295
               grind)
            | exact superpose b5e7295 b5e432
            | exact resolve b5e432 b5e7295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e432 b5e7295
          have b5e7354 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b5e7309 x
               have i₂ := b5e7313 (σ x) x
               grind)
            | exact superpose b5e7313 b5e7309
            | exact resolve b5e7309 b5e7313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7309 b5e7313
          have b5e8527 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e7330 (σ y) X0
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e7330
            | exact resolve b5e7330 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9306 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op (σ y) (σ x)) X0 (σ y)
               have i₂ := b5e7354
               grind)
            | exact superpose b5e7354 b5e13
            | exact resolve b5e13 b5e7354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9364 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b5e9306 x
               have i₂ := b5e7330 x (M.op (σ y) (σ y))
               grind)
            | exact superpose b5e7330 b5e9306
            | exact resolve b5e9306 b5e7330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7330 b5e9306
          have b5e9390 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e9364
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e9364
            | exact resolve b5e9364 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9364
          have b5e10380 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e43 (M.op y y)
               have i₂ := b5e8527 (σ (M.op y y))
               grind)
            | exact superpose b5e8527 b5e43
            | exact resolve b5e43 b5e8527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e8527
          have b5e10513 : (M.op (σ y) (σ x)) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b5e10380
               have i₂ := b5e9390
               grind)
            | exact superpose b5e9390 b5e10380
            | exact resolve b5e10380 b5e9390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9390 b5e10380
          have b5e10561 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e10513
               have i₂ := b5e29 y
               grind)
            | exact superpose b5e29 b5e10513
            | exact resolve b5e10513 b5e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29 b5e10513
          have b5e10718 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e7354
               have i₂ := b5e10561
               grind)
            | exact superpose b5e10561 b5e7354
            | exact resolve b5e7354 b5e10561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7354 b5e10561
          have b5e10779 : False := by grind
          exact b5e10779
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e40 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ x) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) X0 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e40 x
             have i₂ := b6e12 (σ x) x (σ x)
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e45 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e13
          | exact resolve b6e13 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42
        have b6e46 : x = y := by
          first
          | (have i₁ := b6e45
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e45
          | exact resolve b6e45 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e45
        have b6e54 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e46
             grind)
          | exact superpose b6e46 b6e20
          | exact resolve b6e20 b6e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e56 : False := by grind
        exact b6e56
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ y))) := by
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
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X2 X3) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X3 (M.op X3 X0)) X1 (M.op X2 X3)
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e44 (σ X0)
               grind)
            | exact superpose b7e44 b7e19
            | exact resolve b7e19 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e46 X0
               have i₂ := b7e44 X0
               grind)
            | exact superpose b7e44 b7e46
            | exact resolve b7e46 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44 b7e46
          have b7e55 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e57 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e55
          have b7e58 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e23
               grind)
            | exact resolve b7e57 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e59 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e58
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e58
            | exact resolve b7e58 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e62 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e14
            | exact resolve b7e14 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e63 : x = (k x y) := by
            first
            | (have i₁ := b7e62
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e62
            | exact resolve b7e62 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e93 : x = (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e94 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e93
               have r₂ := b7e21
               grind)
            | exact resolve b7e93 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e96 : x = (M.op x y) := by
            first
            | (have r₁ := b7e94
               have r₂ := b7e22
               grind)
            | exact resolve b7e94 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e111 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e13
            | exact resolve b7e13 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e238 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 x (M.op X1 X0)
               have i₂ := b7e30 (M.op (M.op X1 X0) X2) x X1 X0
               grind)
            | exact superpose b7e30 b7e13
            | exact resolve b7e13 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e462 : (σ x) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e29 (σ y)
               have i₂ := b7e51 y
               grind)
            | exact superpose b7e51 b7e29
            | exact resolve b7e29 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e478 : (σ x) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e462
               have i₂ := b7e51 (M.op y y)
               grind)
            | exact superpose b7e51 b7e462
            | exact resolve b7e462 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51 b7e462
          have b7e897 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e238 y x X0
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e238
            | exact resolve b7e238 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e931 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X1 y) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e111 (M.op (M.op X1 y) X0)
               have i₂ := b7e238 y X1 X0
               grind)
            | exact superpose b7e238 b7e111
            | exact resolve b7e111 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e238
          have b7e1247 : y = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b7e897 y
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e897
            | exact resolve b7e897 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e897
          have b7e1551 : (M.op y x) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e111 (M.op y x)
               have i₂ := b7e1247
               grind)
            | exact superpose b7e1247 b7e111
            | exact resolve b7e111 b7e1247
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e1925 : (τ (σ x)) = (M.op (M.op y y) (M.op y y)) := by
            first
            | (have i₁ := b7e14 (M.op (M.op y y) (M.op y y))
               have i₂ := b7e478
               grind)
            | exact superpose b7e478 b7e14
            | exact resolve b7e14 b7e478
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e478
          have b7e1956 : (τ (σ x)) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e1925
               have i₂ := b7e931 (M.op y y) y
               grind)
            | exact superpose b7e931 b7e1925
            | exact resolve b7e1925 b7e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e931 b7e1925
          have b7e1974 : (M.op y x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e1956
               have i₂ := b7e1551
               grind)
            | exact superpose b7e1551 b7e1956
            | exact resolve b7e1956 b7e1551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1551 b7e1956
          have b7e1987 : x = (M.op y x) := by
            first
            | (have i₁ := b7e1974
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1974
            | exact resolve b7e1974 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1974
          have b7e2065 : y = (M.op y x) := by
            first
            | (have i₁ := b7e1247
               have i₂ := b7e1987
               grind)
            | exact superpose b7e1987 b7e1247
            | exact resolve b7e1247 b7e1987
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1247 b7e1987
          have b7e2091 : False := by grind
          exact b7e2091
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X2 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e79 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X2 ∨ (M.op X0 X2) = (k X0 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X2 X1 X0
               have i₂ := b8e18 X0 X2
               grind)
            | (have i₁ := b8e13 X0 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X2
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e85 : ∀ X0 X2 : G, (M.op X0 X2) = (k X0 X2) ∨ X0 = X2 ∨ (M.op X2 X0) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b8e79 X0 x X2
               have i₂ := b8e13 X0 x X0
               grind)
            | exact superpose b8e13 b8e79
            | (have j0 := b8e79 X0 x X2
               grind)
            | exact resolve b8e79 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e109 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e85 (σ X0) (σ X1)
               grind)
            | exact superpose b8e85 b8e19
            | (have j1 := b8e85 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e9726 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e109 x y
               grind)
            | exact superpose b8e109 b8e24
            | (have j1 := b8e109 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e109 x y
               grind)
            | exact resolve b8e24 b8e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e9784 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
          clear b8e9726
          have b8e15022 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e9784
               grind)
            | exact superpose b8e9784 b8e20
            | exact resolve b8e20 b8e9784
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9784
          have b8e15206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e15022
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e15022
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e15022 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15022
          have b8e15214 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e15206
          have b8e15219 : (σ x) = (σ y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e15214
               have r₂ := b8e21
               grind)
            | exact resolve b8e15214 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15214
          have b8e15220 : (σ x) = (σ y) := by
            first
            | (have r₁ := b8e15219
               have r₂ := b8e22
               grind)
            | exact resolve b8e15219 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15219
          have b8e15400 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e15220
               grind)
            | exact superpose b8e15220 b8e23
            | exact resolve b8e23 b8e15220
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15220
          have b8e15440 : False := by grind
          exact b8e15440

/-- `Equation2670`: `x = ((x ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyx_pxx_pyx_pxy_Equation2670 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2670 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2670.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e43 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e44 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e46 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e44
      have b0e47 : (M.op x x) = (k x y) := by grind
      clear b0e43
      have b0e48 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e46
        | exact resolve b0e46 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e49 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e48
           have i₂ := b0e47
           grind)
        | exact superpose b0e47 b0e48
        | exact resolve b0e48 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e48
      have b0e50 : False := by grind
      exact b0e50
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
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
        have b1e52 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b1e54 : (M.op x x) = (k x y) := by grind
        clear b1e52
        have b1e72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          | (have r₁ := b1e16 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e16 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e72
        have b1e76 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e74
             have r₂ := b1e21
             grind)
          | exact resolve b1e74 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e78 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e76
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e76
          | exact resolve b1e76 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76
        have b1e80 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e78
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e78
          | exact resolve b1e78 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e78
        have b1e81 : False := by grind
        exact b1e81
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e51 (σ X0)
             grind)
          | exact superpose b2e51 b2e18
          | exact resolve b2e18 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e54
          | exact resolve b2e54 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e54
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
        have b2e93 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e75 X0 X1
             have i₂ := b2e61 X0
             grind)
          | exact superpose b2e61 b2e75
          | (have j0 := b2e75 X0 X1
             grind)
          | exact resolve b2e75 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61 b2e75
        have b2e746 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e93 x y
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e93 y x
             grind)
          | exact superpose b2e93 b2e22
          | (have j1 := b2e93 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e93 x y
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e93 y x
             grind)
          | exact resolve b2e22 b2e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e796 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
        clear b2e746
        have b2e805 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have r₁ := b2e796
             have r₂ := b2e23
             grind)
          | exact resolve b2e796 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e796
        have b2e821 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e805
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e805
          | exact resolve b2e805 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e805
        have b2e830 : False := by grind
        exact b2e830
  · rcases eq_or_ne (M.op x y) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y x) := by grind
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
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e72 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
          | (have r₁ := b3e16 y x
             have r₂ := b3e21
             grind)
          | exact resolve b3e16 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b3e72
        have b3e77 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e75
             have r₂ := b3e20
             grind)
          | exact resolve b3e75 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e101 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e23
          | exact resolve b3e23 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e55
        have b3e113 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e101
             have i₂ := b3e77
             grind)
          | exact superpose b3e77 b3e101
          | exact resolve b3e101 b3e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77 b3e101
        have b3e114 : False := by grind
        exact b3e114
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : (M.op x y) = (M.op y x) := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e87 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e89
          have b4e92 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          clear b4e87
          have b4e95 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e91
               have r₂ := b4e23
               grind)
            | exact resolve b4e91 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e96 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e92
               have r₂ := b4e21
               grind)
            | exact resolve b4e92 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e98 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e95
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e95
            | exact resolve b4e95 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e100 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e98
               have i₂ := b4e96
               grind)
            | exact superpose b4e96 b4e98
            | exact resolve b4e98 b4e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96 b4e98
          have b4e101 : False := by grind
          exact b4e101
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : (M.op x y) = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b5e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e65 X0
               have i₂ := b5e63 X0
               grind)
            | exact superpose b5e63 b5e65
            | exact resolve b5e65 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e65
          have b5e84 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
            | (have r₁ := b5e17 y x
               have r₂ := b5e22
               grind)
            | exact resolve b5e17 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          clear b5e84
          have b5e89 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b5e87
               have r₂ := b5e21
               grind)
            | exact resolve b5e87 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
          have b5e111 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e94 X0 X1
               have i₂ := b5e74 X0
               grind)
            | exact superpose b5e74 b5e94
            | (have j0 := b5e94 X0 X1
               grind)
            | exact resolve b5e94 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e866 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e111 x y
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e111 y x
               grind)
            | exact superpose b5e111 b5e24
            | (have j1 := b5e111 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e111 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e111 y x
               grind)
            | exact resolve b5e24 b5e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111
          have b5e918 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
          clear b5e866
          have b5e926 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e918
               have i₂ := b5e89
               grind)
            | exact superpose b5e89 b5e918
            | exact resolve b5e918 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e918
          have b5e942 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e926
               have r₂ := b5e20
               grind)
            | exact resolve b5e926 b5e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e926
          have b5e955 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e942
               grind)
            | exact superpose b5e942 b5e23
            | exact resolve b5e23 b5e942
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e942
          have b5e973 : False := by grind
          exact b5e973
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e52 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e52
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e52
          | exact resolve b6e52 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e71 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e23
          | exact resolve b6e23 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e53
        have b6e107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e71
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e71 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e108 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
        clear b6e107
        have b6e109 : (M.op x y) = (M.op y x) := by
          first
          | (have r₁ := b6e108
             have r₂ := b6e20
             grind)
          | exact resolve b6e108 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e108
        have b6e110 : False := by grind
        exact b6e110
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e85 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e17 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e85
          have b7e89 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e23
               grind)
            | exact resolve b7e87 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e91 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e89
            | exact resolve b7e89 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e96 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e91
               grind)
            | exact superpose b7e91 b7e20
            | exact resolve b7e20 b7e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b7e96
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e96
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e96 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e133 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by grind
          clear b7e132
          have b7e134 : (M.op x y) = (M.op y x) := by
            first
            | (have r₁ := b7e133
               have r₂ := b7e21
               grind)
            | exact resolve b7e133 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e135 : False := by grind
          exact b7e135
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          clear b8e61 b8e63
          have b8e97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
          have b8e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e114 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e117 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e97 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e97
            | (have j0 := b8e97 X0 X1
               grind)
            | exact resolve b8e97 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e293 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e114 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e296 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e293 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e293 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e293 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e293 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e293 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293
          have b8e703 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X1) (σ X0)
               have i₂ := b8e117 X0 X1
               grind)
            | (have i₁ := b8e17 (σ X0) (σ X1)
               have i₂ := b8e117 X0 X1
               grind)
            | exact superpose b8e117 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e117 X0 X1
               grind)
            | (have r₁ := b8e17 (σ X0) (σ X1)
               have r₂ := b8e117 X0 X1
               grind)
            | (have r₁ := b8e17 (σ X1) (σ X0)
               have r₂ := b8e117 X0 X1
               grind)
            | exact resolve b8e17 b8e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e746 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e703 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e703
          have b8e752 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e746 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e746
            | (have j0 := b8e746 X0 X1
               grind)
            | exact resolve b8e746 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e746
          have b8e753 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e752 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e752
          have b8e767 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e753 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e753
            | (have j0 := b8e753 X0 X1
               grind)
            | exact resolve b8e753 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e753
          have b8e768 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e767 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e767
          have b8e1642 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e768 X0 X1
               grind)
            | exact superpose b8e768 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e768 X0 X1
               grind)
            | exact resolve b8e16 b8e768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1663 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e768 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e768
          have b8e1671 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1642 X0 X1
               grind)
            | (have r₁ := b8e1642 X0 X1
               have r₂ := b8e72 X0
               grind)
            | exact resolve b8e1642 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1642
          have b8e1700 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1671 X0 X1
               have i₂ := b8e72 X0
               grind)
            | exact superpose b8e72 b8e1671
            | (have j0 := b8e1671 X0 X1
               grind)
            | exact resolve b8e1671 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72 b8e1671
          have b8e1715 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1700 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1700
            | (have j0 := b8e1700 X0 X1
               grind)
            | exact resolve b8e1700 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1700
          have b8e1722 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1715 X0 X1
               have j1 := b8e1663 X0 X1
               grind)
            | (have r₁ := b8e1715 X0 X1
               have r₂ := b8e1663 X0 X1
               grind)
            | exact resolve b8e1715 b8e1663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1663 b8e1715
          have b8e1755 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1722 x y
               grind)
            | exact superpose b8e1722 b8e20
            | exact resolve b8e20 b8e1722
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1722
          have b8e1941 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b8e1755
               have i₂ := b8e296 x y
               grind)
            | exact superpose b8e296 b8e1755
            | (have j1 := b8e296 x y
               grind)
            | exact resolve b8e1755 b8e296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296 b8e1755
          have b8e1946 : (M.op x y) = (M.op y x) := by grind
          clear b8e1941
          have b8e1951 : False := by grind
          exact b8e1951

/-- `Equation3342`: `x ◇ y = y ◇ (x ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_y_pxy_Equation3342 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3342 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3342.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e36 : (M.op x y) = (k x y) := by grind
      have b0e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e37
        | exact resolve b0e37 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e45 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e36
           grind)
        | exact superpose b0e36 b0e43
        | exact resolve b0e43 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e43
      have b0e46 : False := by grind
      exact b0e46
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b1e27 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : (M.op x y) = (k x y) := by grind
        have b1e35 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) := by grind
        have b1e40 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e35
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e35
          | exact resolve b1e35 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e44 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        have b1e48 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e51 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e48
          | exact resolve b1e48 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e54 : (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e34
             grind)
          | exact superpose b1e34 b1e51
          | exact resolve b1e51 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e51
        have b1e59 : (M.op x y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e13
          | exact resolve b1e13 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : y = (M.op x y) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e59
          | exact resolve b1e59 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e84 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b1e93 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e84 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84
        have b1e110 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e27 X0
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e27
          | exact resolve b1e27 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e119 : (k y (M.op x y)) = (M.op y (M.op x y)) := by grind
        clear b1e110
        have b1e126 : (M.op x y) = (k y (M.op x y)) := by
          first
          | (have i₁ := b1e119
             have i₂ := b1e27 y
             grind)
          | exact superpose b1e27 b1e119
          | exact resolve b1e119 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e119
        have b1e129 : y = (k y y) := by
          first
          | (have i₁ := b1e126
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e126
          | exact resolve b1e126 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e311 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
          intro X0 X1
          grind
        clear b1e93
        have b1e321 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e311 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e311
        have b1e835 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e321 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e321
        have b1e896 : y ≠ y ∨ y = (k x y) := by
          first
          | (have i₁ := b1e835 x y
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e835
          | (have j0 := b1e835 x y
             grind)
          | (have r₁ := b1e835 x y
             have r₂ := b1e60
             grind)
          | exact resolve b1e835 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e835
        have b1e902 : y = (k x y) := by grind
        clear b1e896
        have b1e1788 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e92 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e92
          | exact resolve b1e92 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92
        have b1e1988 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e1788
        have b1e2012 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e1988
             have i₂ := b1e129
             grind)
          | exact superpose b1e129 b1e1988
          | exact resolve b1e1988 b1e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e129 b1e1988
        have b1e2013 : (σ x) = (σ y) := by grind
        clear b1e2012
        have b1e2037 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e2013
             grind)
          | exact superpose b1e2013 b1e19
          | exact resolve b1e19 b1e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2040 : (M.op (σ x) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e2013
             grind)
          | exact superpose b1e2013 b1e40
          | exact resolve b1e40 b1e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e2045 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e2013
             grind)
          | exact superpose b1e2013 b1e13
          | exact resolve b1e13 b1e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2046 : ∀ X0 : G, (σ (k y X0)) = (k (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 y X0
             have i₂ := b1e2013
             grind)
          | exact superpose b1e2013 b1e18
          | exact resolve b1e18 b1e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2057 : ∀ X0 : G, (σ (k y X0)) = (σ (k x X0)) := by
          intro X0
          first
          | (have i₁ := b1e2046 X0
             have i₂ := b1e18 x X0
             grind)
          | exact superpose b1e18 b1e2046
          | exact resolve b1e2046 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2046
        have b1e2058 : x = y := by
          first
          | (have i₁ := b1e2045
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e2045
          | exact resolve b1e2045 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2045
        have b1e2061 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e2037
             have i₂ := b1e2040
             grind)
          | exact superpose b1e2040 b1e2037
          | exact resolve b1e2037 b1e2040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2037 b1e2040
        have b1e2063 : (σ (M.op x y)) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e2061
             have i₂ := b1e2057 x
             grind)
          | exact superpose b1e2057 b1e2061
          | exact resolve b1e2061 b1e2057
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2057 b1e2061
        have b1e2064 : (σ y) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e2063
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e2063
          | exact resolve b1e2063 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e2063
        have b1e2065 : (σ x) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b1e2064
             have i₂ := b1e2013
             grind)
          | exact superpose b1e2013 b1e2064
          | exact resolve b1e2064 b1e2013
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2013 b1e2064
        have b1e2297 : x = (k x x) := by
          first
          | (have i₁ := b1e902
             have i₂ := b1e2058
             grind)
          | exact superpose b1e2058 b1e902
          | exact resolve b1e902 b1e2058
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e902 b1e2058
        have b1e3231 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e2065
             have i₂ := b1e2297
             grind)
          | exact superpose b1e2297 b1e2065
          | exact resolve b1e2065 b1e2297
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2065 b1e2297
        have b1e3239 : False := by grind
        exact b1e3239
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : (M.op x y) = (k x y) := by grind
        have b2e81 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 X0 (σ y)
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
        have b2e459 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e81 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e460 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e459
             have r₂ := b2e21
             grind)
          | exact resolve b2e459 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e459
        have b2e461 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e460
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e460
          | exact resolve b2e460 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e460
        have b2e462 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e461
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e461
          | exact resolve b2e461 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e461
        have b2e463 : False := by grind
        exact b2e463
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b3e28 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : (M.op y x) = (k y x) := by grind
        have b3e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e35
          | exact resolve b3e35 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e44 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        have b3e45 : y = (M.op x x) ∨ y = (k x y) := by grind
        have b3e48 : y = (k x y) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e20
             grind)
          | exact resolve b3e45 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e49 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e44
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e44
          | exact resolve b3e44 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e52 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e34
             grind)
          | exact superpose b3e34 b3e49
          | exact resolve b3e49 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e49
        have b3e117 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e19
          | exact resolve b3e19 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e118 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e117
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e117
          | exact resolve b3e117 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e119 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e28 X0
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e28
          | exact resolve b3e28 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e125 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ x) (σ y)))) := by grind
        have b3e128 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e125
             have i₂ := b3e28 (σ x)
             grind)
          | exact superpose b3e28 b3e125
          | exact resolve b3e125 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e125
        have b3e132 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e119 X0
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e119
          | exact resolve b3e119 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119
        have b3e134 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) := by
          first
          | (have i₁ := b3e128
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e128
          | exact resolve b3e128 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e139 : (M.op (σ (k x y)) (σ y)) = (k (σ (k x y)) (σ y)) := by
          first
          | (have i₁ := b3e134
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e134
          | exact resolve b3e134 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134
        have b3e143 : (M.op (σ (k x y)) (σ y)) = (σ (k (k x y) y)) := by
          first
          | (have i₁ := b3e139
             have i₂ := b3e18 (k x y) y
             grind)
          | exact superpose b3e18 b3e139
          | exact resolve b3e139 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e139
        have b3e147 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e143
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e143
          | exact resolve b3e143 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e143
        have b3e151 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e147
             have i₂ := b3e132 (σ y)
             grind)
          | exact superpose b3e132 b3e147
          | exact resolve b3e147 b3e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132 b3e147
        have b3e155 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e151
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e151
          | exact resolve b3e151 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e151
        have b3e156 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e155
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e155
          | exact resolve b3e155 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e155
        have b3e203 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e156
             grind)
          | exact superpose b3e156 b3e13
          | exact resolve b3e13 b3e156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156
        have b3e205 : y = (k y y) := by
          first
          | (have i₁ := b3e203
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e203
          | exact resolve b3e203 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203
        have b3e231 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e205
             grind)
          | exact superpose b3e205 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e205
        have b3e232 : y = (M.op y y) := by grind
        clear b3e231
        have b3e236 : x = y := by
          first
          | (have i₁ := b3e232
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e232
          | exact resolve b3e232 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e232
        have b3e279 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e236
             grind)
          | exact superpose b3e236 b3e19
          | exact resolve b3e19 b3e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e280 : x = (M.op x x) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e236
             grind)
          | exact superpose b3e236 b3e21
          | exact resolve b3e21 b3e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e286 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e236
             grind)
          | exact superpose b3e236 b3e52
          | exact resolve b3e52 b3e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e287 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e118
             have i₂ := b3e236
             grind)
          | exact superpose b3e236 b3e118
          | exact resolve b3e118 b3e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118 b3e236
        have b3e290 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b3e286
             have r₂ := b3e287
             grind)
          | exact resolve b3e286 b3e287
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e286 b3e287
        have b3e294 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e279
             have i₂ := b3e280
             grind)
          | exact superpose b3e280 b3e279
          | exact resolve b3e279 b3e280
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e279 b3e280
        have b3e295 : False := by grind
        exact b3e295
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e28 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e27 X0 X1
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b4e99 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e122 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e32
            | exact resolve b4e32 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e190 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e99 (σ X1) (σ X0)
               grind)
            | exact superpose b4e99 b4e19
            | (have j1 := b4e99 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e192 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 X1
               have i₂ := b4e99 X1 (τ X0)
               grind)
            | exact superpose b4e99 b4e27
            | (have j1 := b4e99 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e197 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          clear b4e99
          have b4e1179 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e197 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197
          have b4e1180 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1179 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1179
          have b4e1420 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e1180 (σ X0)
               grind)
            | exact superpose b4e1180 b4e19
            | exact resolve b4e19 b4e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1422 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e122 X0 X0
               have i₂ := b4e1180 (τ X0)
               grind)
            | exact superpose b4e1180 b4e122
            | exact resolve b4e122 b4e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122
          have b4e1425 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1422 X0
               have i₂ := b4e1180 X0
               grind)
            | exact superpose b4e1180 b4e1422
            | exact resolve b4e1422 b4e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1422
          have b4e1427 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1420 X0
               have i₂ := b4e1180 X0
               grind)
            | exact superpose b4e1180 b4e1420
            | exact resolve b4e1420 b4e1180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1180 b4e1420
          have b4e2102 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ X0) X1
               have i₂ := b4e1427 X0
               grind)
            | exact superpose b4e1427 b4e13
            | exact resolve b4e13 b4e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2105 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            grind
          have b4e2133 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e2105 X0
               have i₂ := b4e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e19 b4e2105
            | exact resolve b4e2105 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2105
          have b4e2142 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            grind
          clear b4e2133
          have b4e5140 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op X1 (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2102 X0 X1
               have i₂ := b4e2142 X0
               grind)
            | exact superpose b4e2142 b4e2102
            | exact resolve b4e2102 b4e2142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2102 b4e2142
          have b4e6087 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (M.op X1 X1))) ∨ (k X0 (σ (M.op X1 (M.op X1 X1)))) = (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X1 (M.op X1 X1))
               have i₂ := b4e192 X0 (M.op X1 (M.op X1 X1))
               grind)
            | exact superpose b4e192 b4e13
            | (have j1 := b4e192 X0 (M.op X1 (M.op X1 X1))
               grind)
            | exact resolve b4e13 b4e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e192
          have b4e6124 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k X0 (σ (M.op X1 (M.op X1 X1)))) = (σ (M.op (τ X0) (M.op X1 (M.op X1 X1)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e6087 X0 X1
               have i₂ := b4e13 X1 X1
               grind)
            | exact superpose b4e13 b4e6087
            | (have j0 := b4e6087 X0 X1
               grind)
            | exact resolve b4e6087 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6087
          have b4e6203 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op X1 X1)))) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e6124 X0 X1
               have i₂ := b4e13 X1 (τ X0)
               grind)
            | exact superpose b4e13 b4e6124
            | (have j0 := b4e6124 X0 X1
               grind)
            | exact resolve b4e6124 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6124
          have b4e9011 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 X1
               have i₂ := b4e190 X1 X0
               grind)
            | exact superpose b4e190 b4e14
            | (have j1 := b4e190 X1 X0
               grind)
            | exact resolve b4e14 b4e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190
          have b4e9167 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e9011 X0 X1
               have i₂ := b4e1427 X0
               grind)
            | exact superpose b4e1427 b4e9011
            | (have j0 := b4e9011 X0 X1
               grind)
            | exact resolve b4e9011 b4e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9011
          have b4e9310 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e9167 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e9167
            | (have j0 := b4e9167 X0 X1
               grind)
            | exact resolve b4e9167 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9167
          have b4e11881 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = X0 ∨ (σ (k X0 (τ X1))) = (M.op (σ X0) (σ (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e1425 X1
               have i₂ := b4e9310 (τ X1) X0
               grind)
            | (have i₁ := b4e1425 X0
               have i₂ := b4e9310 X0 (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e9310 b4e1425
            | (have j1 := b4e9310 (τ X1) X0
               grind)
            | exact resolve b4e1425 b4e9310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1425 b4e9310
          have b4e11999 : ∀ X0 X1 : G, (σ (k X0 (τ X1))) = (M.op (σ X0) X1) ∨ (τ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e11881 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e11881
            | (have j0 := b4e11881 X0 X1
               grind)
            | exact resolve b4e11881 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11881
          have b4e12107 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (τ (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e11999 X0 X1
               have i₂ := b4e28 X1 X0
               grind)
            | exact superpose b4e28 b4e11999
            | (have j0 := b4e11999 X0 X1
               grind)
            | exact resolve b4e11999 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e11999
          have b4e341706 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op X0 (τ (σ X1)))) ∨ (τ (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e12107 X1 (σ (M.op X0 (M.op X0 X0)))
               have i₂ := b4e6203 (σ X1) X0
               grind)
            | exact superpose b4e6203 b4e12107
            | (have j0 := b4e12107 X1 (σ (M.op X0 (M.op X0 X0)))
               have j1 := b4e6203 (σ X1) X0
               grind)
            | exact resolve b4e12107 b4e6203
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6203 b4e12107
          have b4e341764 : ∀ X0 X1 : G, (M.op (σ X1) (σ (M.op X0 (M.op X0 X0)))) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e341706 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e341706
            | (have j0 := b4e341706 X0 X1
               grind)
            | exact resolve b4e341706 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e341706
          have b4e342042 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (τ (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e341764 X0 X1
               have i₂ := b4e5140 X0 (σ X1)
               grind)
            | exact superpose b4e5140 b4e341764
            | (have j0 := b4e341764 X0 X1
               grind)
            | exact resolve b4e341764 b4e5140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5140 b4e341764
          have b4e342277 : ∀ X0 X1 : G, (τ (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e342042 X0 X1
               have i₂ := b4e1427 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b4e1427 b4e342042
            | (have j0 := b4e342042 X0 X1
               grind)
            | exact resolve b4e342042 b4e1427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1427 b4e342042
          have b4e342474 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e342277 X0 X1
               have i₂ := b4e14 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
               grind)
            | exact superpose b4e14 b4e342277
            | (have j0 := b4e342277 X0 X1
               grind)
            | exact resolve b4e342277 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342277
          have b4e342579 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e342474 X0 X1
               have i₂ := b4e13 X0 (M.op X0 (M.op X0 X0))
               grind)
            | exact superpose b4e13 b4e342474
            | (have j0 := b4e342474 X0 X1
               grind)
            | exact resolve b4e342474 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342474
          have b4e342637 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (τ (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e342579 X0 X1
               have i₂ := b4e13 X0 X0
               grind)
            | exact superpose b4e13 b4e342579
            | (have j0 := b4e342579 X0 X1
               grind)
            | exact resolve b4e342579 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342579
          have b4e342680 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e342637 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e342637
            | (have j0 := b4e342637 X0 X1
               grind)
            | exact resolve b4e342637 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342637
          have b4e342681 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e342680 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342680
          have b4e343939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e342681 x y
               grind)
            | exact superpose b4e342681 b4e20
            | (have j1 := b4e342681 x y
               grind)
            | (have r₁ := b4e20
               have r₂ := b4e342681 x y
               grind)
            | exact resolve b4e20 b4e342681
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e342681
          have b4e344276 : y = (M.op x x) := by grind
          clear b4e343939
          have b4e344501 : False := by grind
          exact b4e344501
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e71 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e90 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e128 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          clear b5e90
          have b5e1192 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e128 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e1193 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e1192 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1192
          have b5e1373 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e1193 (σ X0)
               grind)
            | exact superpose b5e1193 b5e19
            | exact resolve b5e19 b5e1193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1380 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1373 X0
               have i₂ := b5e1193 X0
               grind)
            | exact superpose b5e1193 b5e1373
            | exact resolve b5e1373 b5e1193
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1193 b5e1373
          have b5e1787 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1380 y
               grind)
            | exact superpose b5e1380 b5e24
            | exact resolve b5e24 b5e1380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1380
          have b5e1828 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1787
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1787
            | exact resolve b5e1787 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1787
          have b5e1829 : False := by grind
          exact b5e1829
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b6e34 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e34
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e34
          | exact resolve b6e34 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e54 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e89 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e54
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e54 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e90 : y = (M.op x x) ∨ x = (M.op y y) := by grind
        clear b6e89
        have b6e91 : x = (M.op y y) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e75 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e157 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          clear b7e93
          have b7e1072 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e157 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e157
          have b7e1073 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e1072 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1072
          have b7e1287 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e1073 (σ X0)
               grind)
            | exact superpose b7e1073 b7e19
            | exact resolve b7e19 b7e1073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1294 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1287 X0
               have i₂ := b7e1073 X0
               grind)
            | exact superpose b7e1073 b7e1287
            | exact resolve b7e1287 b7e1073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1073 b7e1287
          have b7e1997 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e1294 y
               grind)
            | exact superpose b7e1294 b7e24
            | exact resolve b7e24 b7e1294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1294
          have b7e2443 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e1997
               grind)
            | exact superpose b7e1997 b7e14
            | exact resolve b7e14 b7e1997
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1997
          have b7e2462 : x = (M.op y y) := by
            first
            | (have i₁ := b7e2443
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e2443
            | exact resolve b7e2443 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2443
          have b7e2467 : False := by grind
          exact b7e2467
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e82 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b8e101 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e141 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e101 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e101 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e101 b8e24
            | (have j1 := b8e101 (σ y) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e101 (σ y) (σ x)
               grind)
            | exact resolve b8e24 b8e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e270 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e141 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e271 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e270
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e270
            | exact resolve b8e270 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e270
          have b8e273 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e271
               grind)
            | exact superpose b8e271 b8e20
            | exact resolve b8e20 b8e271
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271
          have b8e279 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e273
               have i₂ := b8e101 y x
               grind)
            | exact superpose b8e101 b8e273
            | (have j1 := b8e101 y x
               grind)
            | exact resolve b8e273 b8e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101 b8e273
          have b8e282 : x = (M.op y y) := by grind
          clear b8e279
          have b8e286 : False := by grind
          exact b8e286

/-- `Equation3736`: `x ◇ y = (x ◇ z) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxy_pyx_Equation3736 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3736 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3736.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e63 (σ X0)
           grind)
        | exact superpose b0e63 b0e17
        | exact resolve b0e17 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e79 X0
           have i₂ := b0e63 X0
           grind)
        | exact superpose b0e63 b0e79
        | exact resolve b0e79 b0e63
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63 b0e79
      have b0e345 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e80 x
           grind)
        | exact superpose b0e80 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e80 x
           grind)
        | exact resolve b0e22 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e80
      have b0e357 : False := by grind
      exact b0e357
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
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
        have b1e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 (M.op X0 X0) X2
             have i₂ := b1e12 X0 X0 X0
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 X0 X1 x
             have i₂ := b1e12 X1 X0 x
             grind)
          | exact superpose b1e12 b1e28
          | exact resolve b1e28 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e30 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b1e27 X0 x X2 X3
             have i₂ := b1e12 X0 X3 x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e45 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 (M.op X0 X1) X2
             have i₂ := b1e30 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b1e30 b1e29
          | exact resolve b1e29 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) X0 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e55 X0
             have i₂ := b1e12 (σ x) X0 (σ x)
             grind)
          | exact superpose b1e12 b1e55
          | exact resolve b1e55 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 (M.op X1 X1)
             have i₂ := b1e29 X1 X0
             grind)
          | exact superpose b1e29 b1e15
          | (have j0 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e15 (M.op X0 X0) X0
             have r₂ := b1e29 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b1e15 X0 (M.op X0 X0)
             have r₂ := b1e29 X0 X0
             grind)
          | exact resolve b1e15 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
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
        have b1e78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e79 : (k x y) = (M.op y x) := by grind
        clear b1e73
        have b1e87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e69 X0 X1
             have i₂ := b1e30 X1 X1 X0
             grind)
          | exact superpose b1e30 b1e69
          | (have j0 := b1e69 X0 X1
             grind)
          | exact resolve b1e69 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69
        have b1e93 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e78 (σ X0)
             grind)
          | exact superpose b1e78 b1e18
          | exact resolve b1e18 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e93 X0
             have i₂ := b1e78 X0
             grind)
          | exact superpose b1e78 b1e93
          | exact resolve b1e93 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 (M.op X1 X1) X1
             have i₂ := b1e12 X1 X1 X1
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 (M.op X0 X0) X1
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e101 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 (M.op X1 X1) (M.op X0 X2)
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e16
          | (have j0 := b1e16 (M.op X1 X1) (M.op X0 X2)
             grind)
          | exact resolve b1e16 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e102 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 (M.op X0 X2)
             have i₂ := b1e30 X0 X2 X1
             grind)
          | exact superpose b1e30 b1e16
          | (have j0 := b1e16 X1 (M.op X0 X2)
             grind)
          | (have r₁ := b1e16 (M.op X0 X2) X0
             have r₂ := b1e30 X0 X2 (M.op X0 X2)
             grind)
          | (have r₁ := b1e16 x (M.op x X2)
             have r₂ := b1e30 x X2 x
             grind)
          | exact resolve b1e16 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e103 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b1e106 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e103
        have b1e107 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e106
             have r₂ := b1e21
             grind)
          | exact resolve b1e106 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e106
        have b1e108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e101 X0 X1 X2
             have i₂ := b1e12 X1 X1 X1
             grind)
          | exact superpose b1e12 b1e101
          | (have j0 := b1e101 X0 X1 X2
             grind)
          | (have r₁ := b1e101 X2 X2 X2
             have r₂ := b1e12 X2 X2 X2
             grind)
          | exact resolve b1e101 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e97 X0 X1
             have i₂ := b1e29 X0 X1
             grind)
          | exact superpose b1e29 b1e97
          | (have j0 := b1e97 X0 X1
             grind)
          | (have r₁ := b1e97 X0 X0
             have r₂ := b1e29 X0 X0
             grind)
          | exact resolve b1e97 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97
        have b1e114 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e107
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e107
          | exact resolve b1e107 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107
        have b1e115 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e108 X0 X1 X2
             have i₂ := b1e12 X1 X1 X1
             grind)
          | exact superpose b1e12 b1e108
          | (have j0 := b1e108 X0 X1 X2
             grind)
          | exact resolve b1e108 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e108
        have b1e119 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e112 X0 X1
             have i₂ := b1e30 X0 X0 X1
             grind)
          | exact superpose b1e30 b1e112
          | (have j0 := b1e112 X0 X1
             grind)
          | (have r₁ := b1e112 (M.op X0 x) X0
             have r₂ := b1e30 X0 x (M.op X0 x)
             grind)
          | (have r₁ := b1e112 x (M.op x x)
             have r₂ := b1e30 x x x
             grind)
          | exact resolve b1e112 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e121 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e114
             have i₂ := b1e79
             grind)
          | exact superpose b1e79 b1e114
          | exact resolve b1e114 b1e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79 b1e114
        have b1e122 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e115 X0 X1 X2
             have i₂ := b1e30 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b1e30 b1e115
          | (have j0 := b1e115 X0 X1 X2
             grind)
          | (have r₁ := b1e115 (M.op X0 X2) X0 X2
             have r₂ := b1e30 X0 X2 X0
             grind)
          | (have r₁ := b1e115 X0 (M.op X0 X2) X2
             have r₂ := b1e30 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b1e115 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115
        have b1e124 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e119 X0 X1
             have i₂ := b1e30 X0 X0 X1
             grind)
          | exact superpose b1e30 b1e119
          | (have j0 := b1e119 X0 X1
             grind)
          | (have r₁ := b1e119 (M.op X0 x) X0
             have r₂ := b1e30 X0 x (M.op X0 x)
             grind)
          | (have r₁ := b1e119 x (M.op x x)
             have r₂ := b1e30 x x x
             grind)
          | exact resolve b1e119 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e119
        have b1e126 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e122 X0 X1 X2
             have i₂ := b1e30 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b1e30 b1e122
          | (have j0 := b1e122 X0 X1 X2
             grind)
          | (have r₁ := b1e122 (M.op X0 X2) X0 X2
             have r₂ := b1e30 X0 X2 X0
             grind)
          | (have r₁ := b1e122 X0 (M.op X0 X2) X2
             have r₂ := b1e30 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b1e122 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e154 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 X1 X2
             have i₂ := b1e17 X1 X0
             grind)
          | (have i₁ := b1e29 X0 X1
             have i₂ := b1e17 X0 X0
             grind)
          | exact superpose b1e17 b1e29
          | (have j1 := b1e17 X1 X0
             grind)
          | exact resolve b1e29 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e183 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e186 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 X0
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e12 X0 X1 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e189 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 X1 X2 X0
             have i₂ := b1e17 X0 (M.op X1 X2)
             grind)
          | (have i₁ := b1e30 X0 X2 (M.op X0 X2)
             have i₂ := b1e17 (M.op X0 X2) X1
             grind)
          | exact superpose b1e17 b1e30
          | (have j1 := b1e17 X0 (M.op X1 X2)
             grind)
          | exact resolve b1e30 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e191 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
        have b1e193 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e194 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e183 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e183
        have b1e195 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e194 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e194
        have b1e198 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e154 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e154
        have b1e199 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e198 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e198
        have b1e200 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e193 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e193 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e193 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e193 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e193
        have b1e201 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e191 X0 X1
             have i₂ := b1e94 X1
             grind)
          | exact superpose b1e94 b1e191
          | (have j0 := b1e191 X0 X1
             grind)
          | exact resolve b1e191 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e191
        have b1e203 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e189 X0 X1 X2
             have j1 := b1e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b1e189 X1 X1 X2
             have r₂ := b1e15 X1 X1
             grind)
          | (have r₁ := b1e189 (M.op X1 X2) X1 X2
             have r₂ := b1e15 (M.op X1 X2) (M.op X1 X2)
             grind)
          | (have r₁ := b1e189 X0 X1 X2
             have r₂ := b1e15 X0 (M.op X1 X2)
             grind)
          | exact resolve b1e189 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e189
        have b1e206 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e186 X0 X1 X2
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e186 X0 (M.op X0 X0) X0
             have r₂ := b1e15 (M.op X0 X0) X0
             grind)
          | (have r₁ := b1e186 X0 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b1e15 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b1e186 X0 X1 X2
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e186 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e186
        have b1e209 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e195 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e195 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e195 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e195 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e195
        have b1e215 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e177 X0 X1 X2
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e177 X0 X0 X0
             have r₂ := b1e15 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b1e177 X0 X1 (M.op X0 X1)
             have r₂ := b1e15 (M.op X0 X1) X1
             grind)
          | (have r₁ := b1e177 X1 X1 X2
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e177 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e177
        have b1e244 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e201 X0 X1
             have i₂ := b1e94 X1
             grind)
          | exact superpose b1e94 b1e201
          | (have j0 := b1e201 X0 X1
             grind)
          | exact resolve b1e201 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e201
        have b1e246 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e203 X0 X1 X2
             have i₂ := b1e30 X1 X2 X0
             grind)
          | exact superpose b1e30 b1e203
          | (have j0 := b1e203 X0 X1 X2
             grind)
          | exact resolve b1e203 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e203
        have b1e249 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e206 X0 X1 X2
             have i₂ := b1e12 X0 X2 X0
             grind)
          | exact superpose b1e12 b1e206
          | (have j0 := b1e206 X0 X1 X2
             grind)
          | exact resolve b1e206 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e206
        have b1e287 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e24 X0 (τ X0)
             have i₂ := b1e78 (τ X0)
             grind)
          | exact superpose b1e78 b1e24
          | exact resolve b1e24 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e291 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b1e292 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e287 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e287
          | exact resolve b1e287 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e287
        have b1e293 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b1e292 X0
             have i₂ := b1e78 X0
             grind)
          | exact superpose b1e78 b1e292
          | exact resolve b1e292 b1e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e78 b1e292
        have b1e301 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e25 X1 X0
             grind)
          | exact superpose b1e25 b1e13
          | exact resolve b1e13 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e307 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e121
             grind)
          | exact superpose b1e121 b1e23
          | exact resolve b1e23 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e391 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (k (M.op X0 X2) X1) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e200 (M.op X0 X2) X1
             have i₂ := b1e30 X0 X2 X1
             grind)
          | exact superpose b1e30 b1e200
          | (have j0 := b1e200 (M.op X0 X2) X1
             grind)
          | exact resolve b1e200 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e402 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e200 x (M.op X0 X2)
             have i₂ := b1e30 X0 X2 x
             grind)
          | exact superpose b1e30 b1e200
          | exact resolve b1e200 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e432 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e56 (σ y)
             have i₂ := b1e94 y
             grind)
          | exact superpose b1e94 b1e56
          | exact resolve b1e56 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e435 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e30 (σ X0) (σ X0) X1
             have i₂ := b1e94 X0
             grind)
          | exact superpose b1e94 b1e30
          | exact resolve b1e30 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e443 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 (σ X0) X1
             have i₂ := b1e94 X0
             grind)
          | exact superpose b1e94 b1e29
          | exact resolve b1e29 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e453 : (σ (M.op y x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e432
             have i₂ := b1e121
             grind)
          | exact superpose b1e121 b1e432
          | exact resolve b1e432 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e432
        have b1e459 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e25 X1 X0
             have i₂ := b1e209 X0 (τ X1)
             grind)
          | exact superpose b1e209 b1e25
          | (have j1 := b1e209 X0 (τ X1)
             grind)
          | exact resolve b1e25 b1e209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e466 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e209 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e209
        have b1e472 : (M.op y y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b1e13 (M.op y y)
             have i₂ := b1e453
             grind)
          | exact superpose b1e453 b1e13
          | exact resolve b1e13 b1e453
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e453
        have b1e473 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b1e472
             have i₂ := b1e13 (M.op y x)
             grind)
          | exact superpose b1e13 b1e472
          | exact resolve b1e472 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e472
        have b1e514 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X1 X2
             have i₂ := b1e249 X2 X0 X1
             grind)
          | (have i₁ := b1e16 X2 X1
             have i₂ := b1e249 X0 X1 X2
             grind)
          | exact superpose b1e249 b1e16
          | (have j0 := b1e16 X1 X2
             have j1 := b1e249 X2 X0 X2
             grind)
          | (have r₁ := b1e16 X2 X1
             have r₂ := b1e249 X2 X1 X2
             grind)
          | (have r₁ := b1e16 X2 X0
             have r₂ := b1e249 X0 X2 X2
             grind)
          | exact resolve b1e16 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e551 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 X1 X2
             have i₂ := b1e249 X0 X1 X1
             grind)
          | (have i₁ := b1e29 X2 X1
             have i₂ := b1e249 X2 X1 X2
             grind)
          | exact superpose b1e249 b1e29
          | (have j1 := b1e249 X0 X1 X2
             grind)
          | exact resolve b1e29 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e604 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b1e29 y X0
             have i₂ := b1e473
             grind)
          | exact superpose b1e473 b1e29
          | exact resolve b1e29 b1e473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1026 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e291 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e291
          | exact resolve b1e291 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1231 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e293 X1
             have i₂ := b1e249 X0 (τ X1) (τ X1)
             grind)
          | (have i₁ := b1e293 X0
             have i₂ := b1e249 (τ X0) X1 (τ X0)
             grind)
          | exact superpose b1e249 b1e293
          | (have j1 := b1e249 X0 (τ X1) x
             grind)
          | exact resolve b1e293 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1381 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e124 X0 X1
             have i₂ := b1e199 X0 X1
             grind)
          | (have i₁ := b1e124 X0 X0
             have i₂ := b1e199 X0 X1
             grind)
          | exact superpose b1e199 b1e124
          | (have j0 := b1e124 X0 X1
             have j1 := b1e199 X0 X1
             grind)
          | (have r₁ := b1e124 X0 X1
             have r₂ := b1e199 X0 X1
             grind)
          | (have r₁ := b1e124 X0 X0
             have r₂ := b1e199 X0 X0
             grind)
          | exact resolve b1e124 b1e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e199
        have b1e1382 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e124 X1 X2
             have i₂ := b1e249 X2 X0 X1
             grind)
          | (have i₁ := b1e124 X2 X1
             have i₂ := b1e249 X0 X1 X2
             grind)
          | exact superpose b1e249 b1e124
          | (have j0 := b1e124 X1 X2
             have j1 := b1e249 X2 X0 X2
             grind)
          | (have r₁ := b1e124 X2 X1
             have r₂ := b1e249 X2 X1 X2
             grind)
          | (have r₁ := b1e124 X2 X0
             have r₂ := b1e249 X0 X2 X2
             grind)
          | exact resolve b1e124 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e1392 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e1381 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1381
        have b1e1399 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e1392 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e1392 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e1392 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e1392 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1392
        have b1e1792 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e126 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e126
        have b1e2345 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e244 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e244
        have b1e4203 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e466 X1 X2
             have i₂ := b1e249 X2 X0 X1
             grind)
          | (have i₁ := b1e466 X2 X1
             have i₂ := b1e249 X0 X1 X2
             grind)
          | exact superpose b1e249 b1e466
          | (have j0 := b1e466 X1 X2
             have j1 := b1e249 X2 X0 X2
             grind)
          | (have r₁ := b1e466 X1 X1
             have r₂ := b1e249 X1 X1 X1
             grind)
          | (have r₁ := b1e466 X0 X0
             have r₂ := b1e249 X0 X0 X0
             grind)
          | exact resolve b1e466 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4207 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X1) X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e466 (M.op X1 X1) X0
             have i₂ := b1e29 X1 X0
             grind)
          | exact superpose b1e29 b1e466
          | (have j0 := b1e466 (M.op X1 X1) X0
             grind)
          | exact resolve b1e466 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4214 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e466 X1 (M.op X0 X2)
             have i₂ := b1e30 X0 X2 X1
             grind)
          | exact superpose b1e30 b1e466
          | (have j0 := b1e466 X1 (M.op X0 X2)
             grind)
          | exact resolve b1e466 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e4252 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e4207 X0 X1
             have i₂ := b1e30 X1 X1 X0
             grind)
          | exact superpose b1e30 b1e4207
          | (have j0 := b1e4207 X0 X1
             grind)
          | (have r₁ := b1e4207 x x
             have r₂ := b1e30 x x x
             grind)
          | exact resolve b1e4207 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4207
        have b1e4281 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e4252 X0 X1
             have i₂ := b1e30 X1 X1 X0
             grind)
          | exact superpose b1e30 b1e4252
          | (have j0 := b1e4252 X0 X1
             grind)
          | exact resolve b1e4252 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4252
        have b1e7108 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e87 X0 X0
             have i₂ := b1e246 X0 X1 X2
             grind)
          | (have i₁ := b1e87 X1 X0
             have i₂ := b1e246 X0 X1 X2
             grind)
          | exact superpose b1e246 b1e87
          | (have j1 := b1e246 X1 X0 X1
             grind)
          | (have r₁ := b1e87 X1 X1
             have r₂ := b1e246 X1 X1 X2
             grind)
          | (have r₁ := b1e87 X0 X0
             have r₂ := b1e246 X0 X0 X2
             grind)
          | exact resolve b1e87 b1e246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e7153 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e246 X0 X1 X2
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e246 X0 X1 X2
             grind)
          | exact superpose b1e246 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e246 X0 X1 X2
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e246 X0 X1 X2
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e246 X0 X0 X2
             grind)
          | exact resolve b1e16 b1e246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7181 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e466 X0 X1
             have i₂ := b1e246 X0 X1 X2
             grind)
          | (have i₁ := b1e466 X0 X0
             have i₂ := b1e246 X0 X1 X2
             grind)
          | exact superpose b1e246 b1e466
          | (have j0 := b1e466 X0 X1
             have j1 := b1e246 X0 X1 X2
             grind)
          | (have r₁ := b1e466 X1 X1
             have r₂ := b1e246 X1 X1 X2
             grind)
          | (have r₁ := b1e466 X0 X0
             have r₂ := b1e246 X0 X0 X2
             grind)
          | exact resolve b1e466 b1e246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e246 b1e466
        have b1e7205 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e7153 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7153
        have b1e7215 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e7108 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7108
        have b1e7242 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e7205 X0 X1 X2
             have j1 := b1e7181 X0 X1 X2
             grind)
          | (have r₁ := b1e7205 X0 X1 X2
             have r₂ := b1e7181 X0 X1 X2
             grind)
          | (have r₁ := b1e7205 X1 X1 X2
             have r₂ := b1e7181 X1 X1 X2
             grind)
          | exact resolve b1e7205 b1e7181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7181 b1e7205
        have b1e11852 : ∀ X0 : G, (M.op y X0) = (k (M.op y x) X0) ∨ (M.op X0 y) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b1e1399 y X0
             have i₂ := b1e473
             grind)
          | exact superpose b1e473 b1e1399
          | (have j0 := b1e1399 y X0
             grind)
          | exact resolve b1e1399 b1e473
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e473 b1e1399
        have b1e29548 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e4281 X2 X1
             have i₂ := b1e249 X2 X0 X1
             grind)
          | (have i₁ := b1e4281 X1 X2
             have i₂ := b1e249 X0 X1 X2
             grind)
          | exact superpose b1e249 b1e4281
          | (have j0 := b1e4281 X2 X1
             have j1 := b1e249 X2 X0 X2
             grind)
          | (have r₁ := b1e4281 X1 X1
             have r₂ := b1e249 X1 X1 X1
             grind)
          | (have r₁ := b1e4281 X0 X0
             have r₂ := b1e249 X0 X0 X0
             grind)
          | exact resolve b1e4281 b1e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e249 b1e4281
        have b1e47244 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op y (M.op X0 X1)) ∨ (k (M.op y x) X0) = (M.op (M.op y x) X0) ∨ (M.op (M.op X0 X1) y) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e7242 (M.op y x) X0 X1
             have i₂ := b1e11852 (M.op X0 X1)
             grind)
          | exact superpose b1e11852 b1e7242
          | (have j0 := b1e7242 (M.op y x) X0 x
             have j1 := b1e11852 (M.op X0 X1)
             grind)
          | exact resolve b1e7242 b1e11852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7242 b1e11852
        have b1e47268 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y (M.op X0 X1)) ∨ (k (M.op y x) X0) = (M.op (M.op y x) X0) ∨ (M.op (M.op X0 X1) y) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e47244 X0 X1
             have i₂ := b1e604 X0
             grind)
          | exact superpose b1e604 b1e47244
          | (have j0 := b1e47244 X0 X1
             grind)
          | exact resolve b1e47244 b1e604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e604 b1e47244
        have b1e47313 : ∀ X0 X1 : G, (M.op y X0) = (k (M.op y x) X0) ∨ (M.op X0 y) = (M.op y (M.op X0 X1)) ∨ (M.op (M.op X0 X1) y) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e47268 X0 X1
             have i₂ := b1e30 y x X0
             grind)
          | exact superpose b1e30 b1e47268
          | (have j0 := b1e47268 X0 X1
             grind)
          | exact resolve b1e47268 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47268
        have b1e47356 : ∀ X0 X1 : G, (M.op X0 y) = (k y (M.op X0 X1)) ∨ (M.op y X0) = (k (M.op y x) X0) ∨ (M.op X0 y) = (M.op y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e47313 X0 X1
             have i₂ := b1e30 X0 X1 y
             grind)
          | exact superpose b1e30 b1e47313
          | (have j0 := b1e47313 X0 X1
             grind)
          | exact resolve b1e47313 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47313
        have b1e47394 : ∀ X0 X1 : G, (M.op X0 y) = (k y (M.op X0 X1)) ∨ (M.op y X0) = (k (M.op y x) X0) := by
          intro X0 X1
          first
          | (have j0 := b1e47356 X0 X1
             have j1 := b1e402 X0 y X1
             grind)
          | (have r₁ := b1e47356 X0 x
             have r₂ := b1e402 X0 y x
             grind)
          | exact resolve b1e47356 b1e402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e402 b1e47356
        have b1e52343 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e1792 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e1792
          | exact resolve b1e1792 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1792
        have b1e52520 : (M.op (σ y) (σ (M.op x x))) = (k (M.op (σ y) (σ y)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52343
             have i₂ := b1e94 x
             grind)
          | exact superpose b1e94 b1e52343
          | exact resolve b1e52343 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52343
        have b1e52674 : (M.op (σ y) (σ (M.op x x))) = (k (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52520
             have i₂ := b1e56 (σ y)
             grind)
          | exact superpose b1e56 b1e52520
          | exact resolve b1e52520 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52520
        have b1e52788 : (M.op (σ y) (σ (M.op x x))) = (k (σ (M.op y x)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52674
             have i₂ := b1e121
             grind)
          | exact superpose b1e121 b1e52674
          | exact resolve b1e52674 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e121 b1e52674
        have b1e52859 : (M.op (σ y) (σ (M.op x x))) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52788
             have i₂ := b1e18 (M.op y x) (M.op x x)
             grind)
          | exact superpose b1e18 b1e52788
          | exact resolve b1e52788 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52788
        have b1e52883 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52859
             have i₂ := b1e56 (σ (M.op x x))
             grind)
          | exact superpose b1e56 b1e52859
          | exact resolve b1e52859 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52859
        have b1e52902 : (M.op (σ x) (σ x)) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52883
             have i₂ := b1e443 x (σ x)
             grind)
          | exact superpose b1e443 b1e52883
          | exact resolve b1e52883 b1e443
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e443 b1e52883
        have b1e52919 : (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b1e52902
             have i₂ := b1e94 x
             grind)
          | exact superpose b1e94 b1e52902
          | exact resolve b1e52902 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52902
        have b1e52929 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
          first
          | (have i₁ := b1e52919
             have i₂ := b1e56 (M.op (σ x) (σ x))
             grind)
          | exact superpose b1e56 b1e52919
          | exact resolve b1e52919 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52919
        have b1e52939 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
          first
          | (have i₁ := b1e52929
             have i₂ := b1e29 (σ x) (σ x)
             grind)
          | exact superpose b1e29 b1e52929
          | exact resolve b1e52929 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52929
        have b1e52943 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
          first
          | (have i₁ := b1e52939
             have i₂ := b1e56 (σ y)
             grind)
          | exact superpose b1e56 b1e52939
          | exact resolve b1e52939 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52939
        have b1e52947 : (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
          first
          | (have r₁ := b1e52943
             have r₂ := b1e21
             grind)
          | exact resolve b1e52943 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52943
        have b1e91443 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e102 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102
        have b1e91479 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e91443 X0 X1
             have j1 := b1e4214 X0 X0 X1
             grind)
          | (have r₁ := b1e91443 X1 x
             have r₂ := b1e4214 X1 X1 x
             grind)
          | exact resolve b1e91443 b1e4214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4214 b1e91443
        have b1e92167 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e91479 (σ y) X0
             have i₂ := b1e56 X0
             grind)
          | exact superpose b1e56 b1e91479
          | exact resolve b1e91479 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92292 : ∀ X0 X1 : G, (τ (M.op (σ X0) (M.op (σ X0) X1))) = (k X0 (τ (M.op (σ X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e301 X0 (M.op (σ X0) X1)
             have i₂ := b1e91479 (σ X0) X1
             grind)
          | exact superpose b1e91479 b1e301
          | exact resolve b1e301 b1e91479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e92377 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e92167 X0
             have i₂ := b1e56 (M.op (σ x) X0)
             grind)
          | exact superpose b1e56 b1e92167
          | exact resolve b1e92167 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92167
        have b1e102649 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e514 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e514
        have b1e102685 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e102649 X0 X1
             have j1 := b1e4203 X0 X0 X1
             grind)
          | (have r₁ := b1e102649 x x
             have r₂ := b1e4203 x x x
             grind)
          | (have r₁ := b1e102649 X0 x
             have r₂ := b1e4203 X0 X0 x
             grind)
          | exact resolve b1e102649 b1e4203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4203 b1e102649
        have b1e105792 : ∀ X0 : G, (τ (M.op (σ x) (M.op (σ x) X0))) = (k y (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b1e301 y (M.op (σ x) X0)
             have i₂ := b1e92377 X0
             grind)
          | exact superpose b1e92377 b1e301
          | exact resolve b1e301 b1e92377
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92377
        have b1e105856 : ∀ X0 : G, (k y (τ (M.op (σ x) X0))) = (k x (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b1e105792 X0
             have i₂ := b1e92292 x X0
             grind)
          | exact superpose b1e92292 b1e105792
          | exact resolve b1e105792 b1e92292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105792
        have b1e107334 : ∀ X0 X1 : G, (τ (M.op (σ X0) (M.op (σ X0) X1))) = (k X0 (τ (M.op (σ X0) (M.op (σ X0) X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e92292 X0 (M.op (σ X0) X1)
             have i₂ := b1e45 (σ X0) X1 (σ X0)
             grind)
          | exact superpose b1e45 b1e92292
          | exact resolve b1e92292 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e107424 : ∀ X0 X1 : G, (k X0 (τ (M.op (σ X0) X1))) = (k X0 (k X0 (τ (M.op (σ X0) X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e107334 X0 X1
             have i₂ := b1e92292 X0 X1
             grind)
          | exact superpose b1e92292 b1e107334
          | exact resolve b1e107334 b1e92292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92292 b1e107334
        have b1e147397 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e2345 (τ X0) (τ X1)
             have i₂ := b1e1026 X0 X1
             grind)
          | exact superpose b1e1026 b1e2345
          | (have j0 := b1e2345 (τ X1) (τ X0)
             grind)
          | exact resolve b1e2345 b1e1026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2345
        have b1e147600 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e147397 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e147397
          | (have j0 := b1e147397 X0 X1
             grind)
          | exact resolve b1e147397 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147397
        have b1e147715 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e147600 X0 X1
             have i₂ := b1e293 X0
             grind)
          | exact superpose b1e293 b1e147600
          | (have j0 := b1e147600 X0 X1
             grind)
          | exact resolve b1e147600 b1e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147600
        have b1e147818 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e147715 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e147715
          | (have j0 := b1e147715 X0 X1
             grind)
          | exact resolve b1e147715 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147715
        have b1e147903 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e147818 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e147818
          | (have j0 := b1e147818 X0 X1
             grind)
          | exact resolve b1e147818 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147818
        have b1e147982 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e147903 X0 X1
             have i₂ := b1e293 X0
             grind)
          | exact superpose b1e293 b1e147903
          | (have j0 := b1e147903 X0 X1
             grind)
          | exact resolve b1e147903 b1e293
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e293 b1e147903
        have b1e148033 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e147982 X0 X1
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e147982
          | (have j0 := b1e147982 X0 X1
             grind)
          | exact resolve b1e147982 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147982
        have b1e148076 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e148033 X0 X1
             have i₂ := b1e14 X1
             grind)
          | exact superpose b1e14 b1e148033
          | (have j0 := b1e148033 X0 X1
             grind)
          | exact resolve b1e148033 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148033
        have b1e148112 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e148076 X0 X1
             have i₂ := b1e14 (k X0 X1)
             grind)
          | exact superpose b1e14 b1e148076
          | (have j0 := b1e148076 X0 X1
             grind)
          | exact resolve b1e148076 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148076
        have b1e148141 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e148112 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e148112 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e148112 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | (have r₁ := b1e148112 X0 X0
             have r₂ := b1e15 X0 X0
             grind)
          | exact resolve b1e148112 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148112
        have b1e148345 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e148141 X0 X1
             have i₂ := b1e102685 X0 X1
             grind)
          | exact superpose b1e102685 b1e148141
          | (have j0 := b1e148141 X1 X0
             have j1 := b1e102685 X0 X1
             grind)
          | (have r₁ := b1e148141 X1 X1
             have r₂ := b1e102685 X1 X1
             grind)
          | exact resolve b1e148141 b1e102685
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102685 b1e148141
        have b1e148469 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e148345 X0 X1
             have j1 := b1e200 X1 X0
             grind)
          | (have r₁ := b1e148345 X0 X1
             have r₂ := b1e200 X0 X1
             grind)
          | (have r₁ := b1e148345 X1 X0
             have r₂ := b1e200 X0 X1
             grind)
          | exact resolve b1e148345 b1e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e200 b1e148345
        have b1e160391 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e1382 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1382
        have b1e160433 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e160391 X0 X1
             have j1 := b1e29548 X0 X0 X1
             grind)
          | (have r₁ := b1e160391 x x
             have r₂ := b1e29548 x x x
             grind)
          | (have r₁ := b1e160391 X0 x
             have r₂ := b1e29548 X0 X0 x
             grind)
          | exact resolve b1e160391 b1e29548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29548 b1e160391
        have b1e227904 : ∀ X0 : G, (k y (τ (M.op (σ x) X0))) = (k y (k y (τ (M.op (σ x) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e107424 y X0
             have i₂ := b1e56 X0
             grind)
          | exact superpose b1e56 b1e107424
          | exact resolve b1e107424 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e107424
        have b1e228368 : ∀ X0 : G, (k x (τ (M.op (σ x) X0))) = (k y (k x (τ (M.op (σ x) X0)))) := by
          intro X0
          first
          | (have i₁ := b1e227904 X0
             have i₂ := b1e105856 X0
             grind)
          | exact superpose b1e105856 b1e227904
          | exact resolve b1e227904 b1e105856
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105856 b1e227904
        have b1e339974 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e459 X1 X0
             have i₂ := b1e1231 X1 X0
             grind)
          | exact superpose b1e1231 b1e459
          | (have j0 := b1e459 X1 X0
             have j1 := b1e1231 X1 X0
             grind)
          | exact resolve b1e459 b1e1231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e459 b1e1231
        have b1e340009 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
          intro X0 X1
          first
          | (have j0 := b1e339974 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e339974
        have b1e341354 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e340009 X1 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e340009
          | (have j0 := b1e340009 X1 (τ X0)
             grind)
          | exact resolve b1e340009 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e340009
        have b1e341538 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e341354 X0 X1
             have i₂ := b1e1026 X1 X0
             grind)
          | exact superpose b1e1026 b1e341354
          | (have j0 := b1e341354 X0 X1
             grind)
          | exact resolve b1e341354 b1e1026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1026 b1e341354
        have b1e343981 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e7215 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7215
        have b1e343982 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b1e343981 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e343981
        have b1e344084 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X1) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e343982 (M.op X1 X1) (M.op X0 x)
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e343982
          | exact resolve b1e343982 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e343982
        have b1e344594 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e160433 X1 (M.op X0 X1)
             have i₂ := b1e344084 X0 X1
             grind)
          | exact superpose b1e344084 b1e160433
          | (have j0 := b1e160433 X1 (M.op X0 X1)
             grind)
          | exact resolve b1e160433 b1e344084
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e160433 b1e344084
        have b1e344627 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e344594 X0 X1
             have j1 := b1e391 X0 X1 X1
             grind)
          | (have r₁ := b1e344594 X0 x
             have r₂ := b1e391 X0 x x
             grind)
          | exact resolve b1e344594 b1e391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e391 b1e344594
        have b1e345622 : ∀ X0 X1 : G, (k (τ (M.op X1 (σ X0))) X0) = (τ (M.op (σ X0) (M.op X1 (σ X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e291 (M.op X1 (σ X0)) X0
             have i₂ := b1e344627 X1 (σ X0)
             grind)
          | exact superpose b1e344627 b1e291
          | exact resolve b1e291 b1e344627
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e344627
        have b1e356340 : ∀ X0 : G, (k (τ (M.op X0 (σ y))) y) = (τ (M.op (σ x) (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b1e345622 y X0
             have i₂ := b1e56 (M.op X0 (σ y))
             grind)
          | exact superpose b1e56 b1e345622
          | exact resolve b1e345622 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e361876 : ∀ X0 X1 X2 : G, (M.op (τ X1) X2) = (M.op (τ (k X0 X1)) X2) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 (τ X1) (τ X0) X2
             have i₂ := b1e341538 X0 X1
             grind)
          | exact superpose b1e341538 b1e30
          | (have j1 := b1e341538 X0 X1
             grind)
          | exact resolve b1e30 b1e341538
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e341538
        have b1e399419 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y (M.op x x))) ∨ (M.op (M.op x x) y) = (k y (M.op (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e52947
             have i₂ := b1e47394 (M.op x x) X0
             grind)
          | exact superpose b1e47394 b1e52947
          | (have j1 := b1e47394 (M.op x x) X0
             grind)
          | exact resolve b1e52947 b1e47394
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47394 b1e52947
        have b1e399435 : ∀ X0 : G, (σ (M.op x x)) = (σ (M.op y x)) ∨ (M.op (M.op x x) y) = (k y (M.op (M.op x x) X0)) := by
          intro X0
          first
          | (have i₁ := b1e399419 X0
             have i₂ := b1e29 x y
             grind)
          | exact superpose b1e29 b1e399419
          | (have j0 := b1e399419 X0
             grind)
          | exact resolve b1e399419 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399419
        have b1e399446 : ∀ X0 : G, (M.op (M.op x x) y) = (k y (M.op (M.op x x) X0)) := by
          intro X0
          first
          | (have j0 := b1e399435 X0
             grind)
          | (have r₁ := b1e399435 X0
             have r₂ := b1e307
             grind)
          | exact resolve b1e399435 b1e307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399435
        have b1e399453 : ∀ X0 : G, (M.op (M.op x x) y) = (k y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e399446 X0
             have i₂ := b1e30 x x X0
             grind)
          | exact superpose b1e30 b1e399446
          | exact resolve b1e399446 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399446
        have b1e399458 : ∀ X0 : G, (M.op x y) = (k y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e399453 X0
             have i₂ := b1e30 x x y
             grind)
          | exact superpose b1e30 b1e399453
          | exact resolve b1e399453 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399453
        have b1e399461 : ∀ X0 : G, (M.op x x) = (k y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e399458 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e399458
          | exact resolve b1e399458 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399458
        have b1e409133 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (τ (σ (k X0 X1))) X2) = (M.op (τ (σ X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e361876 (σ X0) (σ X1) X2
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e361876
          | exact resolve b1e361876 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e361876
        have b1e409218 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (τ (σ (k X0 X1))) X2) = (M.op (τ (σ X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e409133 X0 X1 X2
             have i₂ := b1e94 X1
             grind)
          | exact superpose b1e94 b1e409133
          | (have j0 := b1e409133 X0 X1 X2
             grind)
          | exact resolve b1e409133 b1e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e409133
        have b1e409233 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (τ (σ (k X0 X1))) X2) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e409218 X0 X1 X2
             have i₂ := b1e13 X1
             grind)
          | exact superpose b1e13 b1e409218
          | (have j0 := b1e409218 X0 X1 X2
             grind)
          | exact resolve b1e409218 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e409218
        have b1e409238 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e409233 X0 X1 X2
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e409233
          | (have j0 := b1e409233 X0 X1 X2
             grind)
          | exact resolve b1e409233 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e409233
        have b1e422894 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (τ (σ (k X0 X1))) ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e13 (M.op X1 X1)
             have i₂ := b1e409238 X0 X1 X2
             grind)
          | exact superpose b1e409238 b1e13
          | (have j1 := b1e409238 X0 X1 X2
             grind)
          | exact resolve b1e13 b1e409238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e409238
        have b1e422903 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e422894 X0 X1 X2
             have i₂ := b1e13 (k X0 X1)
             grind)
          | exact superpose b1e13 b1e422894
          | (have j0 := b1e422894 X0 X1 X2
             grind)
          | exact resolve b1e422894 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422894
        have b1e423151 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) ∨ (M.op X1 X3) = (M.op (k X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e30 X1 X1 X2
             have i₂ := b1e422903 X0 X1 X3
             grind)
          | exact superpose b1e422903 b1e30
          | (have j1 := b1e422903 X0 X1 X2
             grind)
          | exact resolve b1e30 b1e422903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422903
        have b1e436819 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e423151 X0 X1 X2 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e423151
        have b1e436820 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (k X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e436819 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e436819
        have b1e437291 : ∀ X0 X1 X2 : G, (M.op (σ X1) X2) = (M.op (σ (k X0 X1)) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e436820 (σ X0) (σ X1) X2
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e436820
          | exact resolve b1e436820 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e439955 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (σ (M.op x X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e437291 y (M.op x X0) X1
             have i₂ := b1e399461 X0
             grind)
          | exact superpose b1e399461 b1e437291
          | exact resolve b1e437291 b1e399461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e440230 : ∀ X0 X1 : G, (σ (M.op (k X1 X0) (k X1 X0))) = (M.op (σ X0) (σ (k X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e94 (k X1 X0)
             have i₂ := b1e437291 X1 X0 (σ (k X1 X0))
             grind)
          | exact superpose b1e437291 b1e94
          | exact resolve b1e94 b1e437291
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e437291
        have b1e440701 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X1 X0))) = (σ (M.op X0 (k X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e440230 X0 X1
             have i₂ := b1e436820 X1 X0 (k X1 X0)
             grind)
          | exact superpose b1e436820 b1e440230
          | exact resolve b1e440230 b1e436820
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e436820 b1e440230
        have b1e440847 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ (M.op x X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e439955 X0 X1
             have i₂ := b1e435 x X1
             grind)
          | exact superpose b1e435 b1e439955
          | exact resolve b1e439955 b1e435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e435 b1e439955
        have b1e443015 : ∀ X0 : G, (M.op (σ x) (σ (M.op x X0))) = (σ (M.op (M.op x X0) (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b1e94 (M.op x X0)
             have i₂ := b1e440847 X0 (σ (M.op x X0))
             grind)
          | exact superpose b1e440847 b1e94
          | exact resolve b1e94 b1e440847
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e94 b1e440847
        have b1e443478 : ∀ X0 : G, (M.op (σ x) (σ (M.op x X0))) = (σ (M.op x (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b1e443015 X0
             have i₂ := b1e30 x X0 (M.op x X0)
             grind)
          | exact superpose b1e30 b1e443015
          | exact resolve b1e443015 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e443015
        have b1e511656 : ∀ X0 : G, (k x (τ (σ (M.op x (M.op x X0))))) = (k y (k x (τ (σ (M.op x (M.op x X0)))))) := by
          intro X0
          first
          | (have i₁ := b1e228368 (σ (M.op x X0))
             have i₂ := b1e443478 X0
             grind)
          | exact superpose b1e443478 b1e228368
          | exact resolve b1e228368 b1e443478
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228368
        have b1e511761 : ∀ X0 : G, (k x (M.op x (M.op x X0))) = (k y (k x (M.op x (M.op x X0)))) := by
          intro X0
          first
          | (have i₁ := b1e511656 X0
             have i₂ := b1e13 (M.op x (M.op x X0))
             grind)
          | exact superpose b1e13 b1e511656
          | exact resolve b1e511656 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e511656
        have b1e511804 : ∀ X0 : G, (M.op x (M.op x (M.op x X0))) = (k y (M.op x (M.op x (M.op x X0)))) := by
          intro X0
          first
          | (have i₁ := b1e511761 X0
             have i₂ := b1e91479 x (M.op x X0)
             grind)
          | exact superpose b1e91479 b1e511761
          | exact resolve b1e511761 b1e91479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91479 b1e511761
        have b1e511818 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b1e511804 X0
             have i₂ := b1e399461 (M.op x (M.op x X0))
             grind)
          | exact superpose b1e399461 b1e511804
          | exact resolve b1e511804 b1e399461
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e399461 b1e511804
        have b1e511826 : ∀ X0 : G, (M.op x x) = (M.op x (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b1e511818 X0
             have i₂ := b1e45 x X0 x
             grind)
          | exact superpose b1e45 b1e511818
          | exact resolve b1e511818 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e511818
        have b1e512157 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = (M.op X0 (M.op x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e45 x X1 X0
             have i₂ := b1e511826 X1
             grind)
          | exact superpose b1e511826 b1e45
          | exact resolve b1e45 b1e511826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e512202 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b1e215 x X0 x
             have i₂ := b1e511826 X0
             grind)
          | exact superpose b1e511826 b1e215
          | (have j0 := b1e215 x X0 x
             grind)
          | exact resolve b1e215 b1e511826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e215
        have b1e512207 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e551 x X0 x
             have i₂ := b1e511826 X0
             grind)
          | exact superpose b1e511826 b1e551
          | (have j0 := b1e551 x X0 x
             grind)
          | exact resolve b1e551 b1e511826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e551
        have b1e512617 : ∀ X0 : G, (k x X0) = (M.op X0 x) := by
          intro X0
          first
          | (have j0 := b1e512207 X0
             have j1 := b1e15 x X0
             grind)
          | (have r₁ := b1e512207 x
             have r₂ := b1e15 x x
             grind)
          | (have r₁ := b1e512207 x
             have r₂ := b1e15 x x
             grind)
          | exact resolve b1e512207 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512207
        have b1e512621 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
          intro X0
          first
          | (have j0 := b1e512202 X0
             have j1 := b1e148469 x X0
             grind)
          | (have r₁ := b1e512202 x
             have r₂ := b1e148469 x x
             grind)
          | (have r₁ := b1e512202 x
             have r₂ := b1e148469 x x
             grind)
          | exact resolve b1e512202 b1e148469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148469 b1e512202
        have b1e512636 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e512157 X0 X1
             have i₂ := b1e29 x X0
             grind)
          | exact superpose b1e29 b1e512157
          | exact resolve b1e512157 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e512157
        have b1e513202 : ∀ X0 : G, (τ (M.op (σ X0) x)) = (k (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e291 x X0
             have i₂ := b1e512617 (σ X0)
             grind)
          | exact superpose b1e512617 b1e291
          | exact resolve b1e291 b1e512617
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e291 b1e512617
        have b1e514181 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k X0 (τ x)) := by
          intro X0
          first
          | (have i₁ := b1e301 X0 x
             have i₂ := b1e512621 (σ X0)
             grind)
          | exact superpose b1e512621 b1e301
          | exact resolve b1e301 b1e512621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e301
        have b1e516876 : ∀ X0 : G, (τ (M.op (σ X0) x)) = (k (τ (M.op x (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e345622 X0 x
             have i₂ := b1e512636 (σ X0) (σ X0)
             grind)
          | exact superpose b1e512636 b1e345622
          | exact resolve b1e345622 b1e512636
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e345622
        have b1e516878 : (τ (M.op (σ x) x)) = (k (τ (M.op x (σ y))) y) := by
          first
          | (have i₁ := b1e356340 x
             have i₂ := b1e512636 (σ x) (σ y)
             grind)
          | exact superpose b1e512636 b1e356340
          | exact resolve b1e356340 b1e512636
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e356340
        have b1e517409 : (τ (M.op (σ x) x)) = (k (k y (τ x)) y) := by
          first
          | (have i₁ := b1e516878
             have i₂ := b1e514181 y
             grind)
          | exact superpose b1e514181 b1e516878
          | exact resolve b1e516878 b1e514181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e516878
        have b1e517411 : ∀ X0 : G, (τ (M.op (σ X0) x)) = (k (k X0 (τ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e516876 X0
             have i₂ := b1e514181 X0
             grind)
          | exact superpose b1e514181 b1e516876
          | exact resolve b1e516876 b1e514181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e514181 b1e516876
        have b1e517873 : (k (τ x) x) = (k (k y (τ x)) y) := by
          first
          | (have i₁ := b1e517409
             have i₂ := b1e513202 x
             grind)
          | exact superpose b1e513202 b1e517409
          | exact resolve b1e517409 b1e513202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e517409
        have b1e517874 : ∀ X0 : G, (k (τ x) X0) = (k (k X0 (τ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e517411 X0
             have i₂ := b1e513202 X0
             grind)
          | exact superpose b1e513202 b1e517411
          | exact resolve b1e517411 b1e513202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e513202 b1e517411
        have b1e517983 : (M.op x (τ x)) = (k (k y (τ x)) y) := by
          first
          | (have i₁ := b1e517873
             have i₂ := b1e512621 (τ x)
             grind)
          | exact superpose b1e512621 b1e517873
          | exact resolve b1e517873 b1e512621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512621 b1e517873
        have b1e518021 : (k (τ x) y) = (M.op x (τ x)) := by
          first
          | (have i₁ := b1e517983
             have i₂ := b1e517874 y
             grind)
          | exact superpose b1e517874 b1e517983
          | exact resolve b1e517983 b1e517874
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e517874 b1e517983
        have b1e521021 : (M.op (σ y) (σ (M.op x (τ x)))) = (σ (M.op y (M.op x (τ x)))) := by
          first
          | (have i₁ := b1e440701 y (τ x)
             have i₂ := b1e518021
             grind)
          | exact superpose b1e518021 b1e440701
          | exact resolve b1e440701 b1e518021
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e440701 b1e518021
        have b1e521035 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op x (τ x)))) := by
          first
          | (have i₁ := b1e521021
             have i₂ := b1e512636 y (τ x)
             grind)
          | exact superpose b1e512636 b1e521021
          | exact resolve b1e521021 b1e512636
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e512636 b1e521021
        have b1e521204 : (σ (M.op y x)) = (M.op (σ x) (σ (M.op x (τ x)))) := by
          first
          | (have i₁ := b1e521035
             have i₂ := b1e56 (σ (M.op x (τ x)))
             grind)
          | exact superpose b1e56 b1e521035
          | exact resolve b1e521035 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e521035
        have b1e521264 : (σ (M.op y x)) = (σ (M.op x (M.op x (τ x)))) := by
          first
          | (have i₁ := b1e521204
             have i₂ := b1e443478 (τ x)
             grind)
          | exact superpose b1e443478 b1e521204
          | exact resolve b1e521204 b1e443478
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e443478 b1e521204
        have b1e521293 : (σ (M.op x x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e521264
             have i₂ := b1e511826 (τ x)
             grind)
          | exact superpose b1e511826 b1e521264
          | exact resolve b1e521264 b1e511826
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e511826 b1e521264
        have b1e521304 : False := by grind
        exact b1e521304
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op X0 X0) X2
             have i₂ := b2e12 X0 X0 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 X1 x
             have i₂ := b2e12 X1 X0 x
             grind)
          | exact superpose b2e12 b2e28
          | exact resolve b2e28 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e30 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e27 X0 x X2 X3
             have i₂ := b2e12 X0 X3 x
             grind)
          | exact superpose b2e12 b2e27
          | exact resolve b2e27 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e58 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y x) := by
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
        have b2e62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (M.op X0 X0) X1
             have i₂ := b2e12 X0 X0 X0
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 (M.op X0 X0) X1
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : (k x y) = (M.op y x) := by grind
        clear b2e58
        have b2e69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e62 X0 X1
             have i₂ := b2e30 X0 X0 X1
             grind)
          | exact superpose b2e30 b2e62
          | (have j0 := b2e62 X0 X1
             grind)
          | (have r₁ := b2e62 x x
             have r₂ := b2e30 x x x
             grind)
          | exact resolve b2e62 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e62
        have b2e74 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e69 X0 X1
             have i₂ := b2e29 X0 X1
             grind)
          | exact superpose b2e29 b2e69
          | (have j0 := b2e69 X0 X1
             grind)
          | (have r₁ := b2e69 (M.op X0 X0) X0
             have r₂ := b2e29 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b2e69 X0 (M.op X0 X0)
             have r₂ := b2e29 X0 X0
             grind)
          | exact resolve b2e69 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e69
        have b2e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e65 (σ X0)
             grind)
          | exact superpose b2e65 b2e18
          | exact resolve b2e18 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e78 X0
             have i₂ := b2e65 X0
             grind)
          | exact superpose b2e65 b2e78
          | exact resolve b2e78 b2e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e65 b2e78
        have b2e129 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e158 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 X0
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e12 X0 X1 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X0 X1
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e170 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e129 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129
        have b2e171 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e170 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e170
        have b2e177 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e158 X0 X1 X2
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e158 X0 (M.op X0 X0) X0
             have r₂ := b2e15 (M.op X0 X0) X0
             grind)
          | (have r₁ := b2e158 X0 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b2e15 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b2e158 X0 X1 X2
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e158 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e158
        have b2e214 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e177 X0 X1 X2
             have i₂ := b2e12 X0 X2 X0
             grind)
          | exact superpose b2e12 b2e177
          | (have j0 := b2e177 X0 X1 X2
             grind)
          | exact resolve b2e177 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e177
        have b2e478 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e214 (σ y) X0 (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e214 X0 (σ y) (σ x)
             grind)
          | exact superpose b2e214 b2e22
          | (have j1 := b2e214 (σ y) X0 x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e214 (σ x) (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e214 (σ y) (σ x) (σ x)
             grind)
          | exact resolve b2e22 b2e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e502 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e214 X0 (σ y) (σ x)
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e214 (σ y) x (σ x)
             grind)
          | exact superpose b2e214 b2e22
          | (have j1 := b2e214 X0 (σ y) x
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e214 (σ x) (σ y) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e214 (σ y) (σ x) (σ x)
             grind)
          | exact resolve b2e22 b2e214
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e214
        have b2e509 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e502 X0
             have i₂ := b2e81 x
             grind)
          | exact superpose b2e81 b2e502
          | (have j0 := b2e502 X0
             grind)
          | exact resolve b2e502 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e502
        have b2e517 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e478 X0
             have i₂ := b2e81 x
             grind)
          | exact superpose b2e81 b2e478
          | (have j0 := b2e478 X0
             grind)
          | exact resolve b2e478 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e478
        have b2e568 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e74 X0 X0
             have i₂ := b2e171 X0 X1
             grind)
          | (have i₁ := b2e74 X1 X0
             have i₂ := b2e171 X0 X1
             grind)
          | exact superpose b2e171 b2e74
          | (have j1 := b2e171 X1 X0
             grind)
          | (have r₁ := b2e74 X1 X1
             have r₂ := b2e171 X1 X1
             grind)
          | (have r₁ := b2e74 X0 X0
             have r₂ := b2e171 X0 X0
             grind)
          | exact resolve b2e74 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171
        have b2e574 : (M.op x x) ≠ (M.op x x) ∨ (M.op y x) = (k (M.op x x) y) := by
          first
          | (have i₁ := b2e74 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e74
          | (have j0 := b2e74 x x
             grind)
          | (have r₁ := b2e74 x y
             have r₂ := b2e20
             grind)
          | exact resolve b2e74 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e74
        have b2e585 : (M.op y x) = (k (M.op x x) y) := by grind
        clear b2e574
        have b2e589 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e568 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e568
        have b2e7361 : (M.op x x) = (k (M.op x x) y) ∨ (M.op x x) = (k y x) := by
          first
          | (have i₁ := b2e589 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e589
          | exact resolve b2e589 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e589
        have b2e7389 : (M.op x x) = (k y x) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b2e7361
             have i₂ := b2e585
             grind)
          | exact superpose b2e585 b2e7361
          | exact resolve b2e7361 b2e585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e585 b2e7361
        have b2e14459 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b2e509 (σ x)
             have i₂ := b2e81 x
             grind)
          | exact superpose b2e81 b2e509
          | (have j0 := b2e509 (σ x)
             grind)
          | (have r₁ := b2e509 (σ x)
             have r₂ := b2e81 x
             grind)
          | exact resolve b2e509 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e509
        have b2e14470 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b2e14459
        have b2e14480 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e14470
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e14470
          | exact resolve b2e14470 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14470
        have b2e14488 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e14480
             have i₂ := b2e66
             grind)
          | exact superpose b2e66 b2e14480
          | exact resolve b2e14480 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66 b2e14480
        have b2e14495 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e14488
             grind)
          | exact superpose b2e14488 b2e22
          | exact resolve b2e22 b2e14488
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14488
        have b2e14569 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e14495
             have i₂ := b2e81 x
             grind)
          | exact superpose b2e81 b2e14495
          | exact resolve b2e14495 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14495
        have b2e14599 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b2e517 (σ x)
             have i₂ := b2e81 x
             grind)
          | exact superpose b2e81 b2e517
          | (have j0 := b2e517 (σ x)
             grind)
          | (have r₁ := b2e517 (σ x)
             have r₂ := b2e81 x
             grind)
          | exact resolve b2e517 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81 b2e517
        have b2e14611 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b2e14599
        have b2e14621 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b2e14611
             have i₂ := b2e18 y x
             grind)
          | exact superpose b2e18 b2e14611
          | exact resolve b2e14611 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14611
        have b2e15040 : (σ (M.op x x)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e14621
             grind)
          | exact superpose b2e14621 b2e23
          | exact resolve b2e23 b2e14621
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e14621
        have b2e15236 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b2e15040
             have i₂ := b2e7389
             grind)
          | exact superpose b2e7389 b2e15040
          | exact resolve b2e15040 b2e7389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7389 b2e15040
        have b2e15245 : (M.op x x) = (M.op y x) := by grind
        clear b2e15236
        have b2e15846 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e14569
             have i₂ := b2e15245
             grind)
          | exact superpose b2e15245 b2e14569
          | exact resolve b2e14569 b2e15245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e14569 b2e15245
        have b2e15888 : False := by grind
        exact b2e15888
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x x) = (M.op y x) := by grind
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
        have b3e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 (τ X0) X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e18 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e18
          | exact resolve b3e18 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e24 X0 X1
             grind)
          | exact superpose b3e24 b3e13
          | exact resolve b3e13 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x x) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 (M.op X0 X0) X2
             have i₂ := b3e12 X0 X0 X0
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X0 X1 x
             have i₂ := b3e12 X1 X0 x
             grind)
          | exact superpose b3e12 b3e32
          | exact resolve b3e32 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e34 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b3e31 X0 x X2 X3
             have i₂ := b3e12 X0 X3 x
             grind)
          | exact superpose b3e12 b3e31
          | exact resolve b3e31 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e35 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e30 X0
             have i₂ := b3e12 x X0 x
             grind)
          | exact superpose b3e12 b3e30
          | exact resolve b3e30 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e37 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 y X1
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e12
          | exact resolve b3e12 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e37 X0 x
             have i₂ := b3e34 X0 x (M.op x y)
             grind)
          | exact superpose b3e34 b3e37
          | exact resolve b3e37 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e52 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 (M.op X1 X1)
             have i₂ := b3e33 X1 X0
             grind)
          | exact superpose b3e33 b3e15
          | (have j0 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e15 (M.op X0 X0) X0
             have r₂ := b3e33 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e15 X0 (M.op X0 X0)
             have r₂ := b3e33 X0 X0
             grind)
          | exact resolve b3e15 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X2) (M.op X0 X2)) ∨ (k (M.op X0 X2) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e15 (M.op X0 X2) (M.op X1 X1)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 (M.op X0 X2) (M.op X1 X1)
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e57 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 (M.op X0 X0) X1
             have i₂ := b3e12 X0 X0 X0
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 (M.op X0 X0) X1
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : ∀ X0 : G, (M.op x y) ≠ (M.op y X0) ∨ (M.op X0 y) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e15 y X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e15
          | (have j0 := b3e15 y X0
             grind)
          | exact resolve b3e15 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e59 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e54
        have b3e61 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 y) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e58
          | (have j0 := b3e58 X0
             grind)
          | (have r₁ := b3e58 y
             have r₂ := b3e35 y
             grind)
          | exact resolve b3e58 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e62 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e57 X0 X1
             have i₂ := b3e34 X0 X0 X1
             grind)
          | exact superpose b3e34 b3e57
          | (have j0 := b3e57 X0 X1
             grind)
          | (have r₁ := b3e57 x x
             have r₂ := b3e34 x x x
             grind)
          | exact resolve b3e57 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e65 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e60
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e60
          | exact resolve b3e60 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e66 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (k (M.op X0 X2) (M.op X1 X1)) = (M.op (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e53 X0 X1 X2
             have i₂ := b3e34 X0 X2 (M.op X0 X2)
             grind)
          | exact superpose b3e34 b3e53
          | (have j0 := b3e53 X0 X1 X2
             grind)
          | (have r₁ := b3e53 X0 (M.op X0 X2) X2
             have r₂ := b3e34 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b3e53 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53
        have b3e67 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e52 X0 X1
             have i₂ := b3e34 X1 X1 X0
             grind)
          | exact superpose b3e34 b3e52
          | (have j0 := b3e52 X0 X1
             grind)
          | exact resolve b3e52 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e62 X0 X1
             have i₂ := b3e33 X0 X1
             grind)
          | exact superpose b3e33 b3e62
          | (have j0 := b3e62 X0 X1
             grind)
          | (have r₁ := b3e62 (M.op X0 X0) X0
             have r₂ := b3e33 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e62 X0 (M.op X0 X0)
             have r₂ := b3e33 X0 X0
             grind)
          | exact resolve b3e62 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e70 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X0 X2)) ∨ (k (M.op X0 X2) (M.op X1 X1)) = (M.op X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e66 X0 X1 X2
             have i₂ := b3e34 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b3e34 b3e66
          | (have j0 := b3e66 X0 X1 X2
             grind)
          | exact resolve b3e66 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e59 (σ X0)
             grind)
          | exact superpose b3e59 b3e18
          | exact resolve b3e18 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e74 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e24 X0 (τ X0)
             have i₂ := b3e59 (τ X0)
             grind)
          | exact superpose b3e59 b3e24
          | exact resolve b3e24 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e75 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e74 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e74
          | exact resolve b3e74 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e73 X0
             have i₂ := b3e59 X0
             grind)
          | exact superpose b3e59 b3e73
          | exact resolve b3e73 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e78 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have i₁ := b3e75 X0
             have i₂ := b3e59 X0
             grind)
          | exact superpose b3e59 b3e75
          | exact resolve b3e75 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 (M.op X1 X1) X1
             have i₂ := b3e12 X1 X1 X1
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 (M.op X0 X0) X1
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e83 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 (M.op X1 X1) (M.op X0 X2)
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e16
          | (have j0 := b3e16 (M.op X1 X1) (M.op X0 X2)
             grind)
          | exact resolve b3e16 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
        have b3e85 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 y x
             have r₂ := b3e35 y
             grind)
          | (have r₁ := b3e16 x y
             have r₂ := b3e35 x
             grind)
          | exact resolve b3e16 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e87 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        clear b3e84
        have b3e88 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e87
             have r₂ := b3e20
             grind)
          | exact resolve b3e87 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e89 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e83 X0 X1 X2
             have i₂ := b3e12 X1 X1 X1
             grind)
          | exact superpose b3e12 b3e83
          | (have j0 := b3e83 X0 X1 X2
             grind)
          | (have r₁ := b3e83 X2 X2 X2
             have r₂ := b3e12 X2 X2 X2
             grind)
          | exact resolve b3e83 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e80 X0 X1
             have i₂ := b3e33 X0 X1
             grind)
          | exact superpose b3e33 b3e80
          | (have j0 := b3e80 X0 X1
             grind)
          | (have r₁ := b3e80 X0 X0
             have r₂ := b3e33 X0 X0
             grind)
          | exact resolve b3e80 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e94 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e89 X0 X1 X2
             have i₂ := b3e12 X1 X1 X1
             grind)
          | exact superpose b3e12 b3e89
          | (have j0 := b3e89 X0 X1 X2
             grind)
          | exact resolve b3e89 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89
        have b3e97 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e92 X0 X1
             have i₂ := b3e34 X0 X0 X1
             grind)
          | exact superpose b3e34 b3e92
          | (have j0 := b3e92 X0 X1
             grind)
          | (have r₁ := b3e92 (M.op X0 x) X0
             have r₂ := b3e34 X0 x (M.op X0 x)
             grind)
          | (have r₁ := b3e92 x (M.op x x)
             have r₂ := b3e34 x x x
             grind)
          | exact resolve b3e92 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e92
        have b3e99 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e94 X0 X1 X2
             have i₂ := b3e34 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b3e34 b3e94
          | (have j0 := b3e94 X0 X1 X2
             grind)
          | (have r₁ := b3e94 (M.op X0 X2) X0 X2
             have r₂ := b3e34 X0 X2 X0
             grind)
          | (have r₁ := b3e94 X0 (M.op X0 X2) X2
             have r₂ := b3e34 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b3e94 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e97 X0 X1
             have i₂ := b3e34 X0 X0 X1
             grind)
          | exact superpose b3e34 b3e97
          | (have j0 := b3e97 X0 X1
             grind)
          | (have r₁ := b3e97 (M.op X0 x) X0
             have r₂ := b3e34 X0 x (M.op X0 x)
             grind)
          | (have r₁ := b3e97 x (M.op x x)
             have r₂ := b3e34 x x x
             grind)
          | exact resolve b3e97 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97
        have b3e103 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e99 X0 X1 X2
             have i₂ := b3e34 X1 X1 (M.op X0 X2)
             grind)
          | exact superpose b3e34 b3e99
          | (have j0 := b3e99 X0 X1 X2
             grind)
          | (have r₁ := b3e99 (M.op X0 X2) X0 X2
             have r₂ := b3e34 X0 X2 X0
             grind)
          | (have r₁ := b3e99 X0 (M.op X0 X2) X2
             have r₂ := b3e34 X0 X2 (M.op X0 X2)
             grind)
          | exact resolve b3e99 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e99
        have b3e125 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e127 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op (M.op X1 X1) X0) ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 X1 X0
             have i₂ := b3e17 X0 (M.op X1 X1)
             grind)
          | (have i₁ := b3e33 X0 (M.op X0 X0)
             have i₂ := b3e17 (M.op X0 X0) X1
             grind)
          | exact superpose b3e17 b3e33
          | (have j1 := b3e17 X0 (M.op X1 X1)
             grind)
          | exact resolve b3e33 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e142 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e33 X1 X2
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e33 X0 X1
             have i₂ := b3e17 X0 X0
             grind)
          | exact superpose b3e17 b3e33
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e33 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e146 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e23
             have i₂ := b3e17 (σ x) X0
             grind)
          | (have i₁ := b3e23
             have i₂ := b3e17 (σ x) (σ x)
             grind)
          | exact superpose b3e17 b3e23
          | (have j1 := b3e17 (σ x) X0
             grind)
          | exact resolve b3e23 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e147 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e149 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e12 X0 X1 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X1
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e152 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e35 X0
             have i₂ := b3e17 X0 y
             grind)
          | (have i₁ := b3e35 y
             have i₂ := b3e17 y x
             grind)
          | exact superpose b3e17 b3e35
          | (have j1 := b3e17 X0 y
             grind)
          | exact resolve b3e35 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e153 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
        have b3e157 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e147 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e147
        have b3e159 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e158 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158
        have b3e162 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e125 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e125
        have b3e163 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e162 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e162
        have b3e164 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e157 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e157 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e157 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e157 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e157
        have b3e165 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e153 X0 X1
             have i₂ := b3e76 X1
             grind)
          | exact superpose b3e76 b3e153
          | (have j0 := b3e153 X0 X1
             grind)
          | exact resolve b3e153 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153
        have b3e166 : ∀ X0 : G, (M.op X0 X0) = (M.op x X0) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e152 X0
             have j1 := b3e15 X0 y
             grind)
          | (have r₁ := b3e152 x
             have r₂ := b3e15 x x
             grind)
          | (have r₁ := b3e152 y
             have r₂ := b3e15 y y
             grind)
          | (have r₁ := b3e152 X0
             have r₂ := b3e15 X0 y
             grind)
          | exact resolve b3e152 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152
        have b3e169 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e149 X0 X1 X2
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e149 X0 (M.op X0 X0) X0
             have r₂ := b3e15 (M.op X0 X0) X0
             grind)
          | (have r₁ := b3e149 X0 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b3e15 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b3e149 X0 X1 X2
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e149 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e149
        have b3e171 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e159 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e159 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e159 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e159 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e159
        have b3e172 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e146 X0
             have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e146 (σ x)
             have r₂ := b3e15 (σ x) (σ x)
             grind)
          | (have r₁ := b3e146 x
             have r₂ := b3e15 (σ x) x
             grind)
          | exact resolve b3e146 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146
        have b3e176 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e142 X0 X1 X2
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e142 X0 X1 (M.op X0 X1)
             have r₂ := b3e15 (M.op X0 X1) X1
             grind)
          | (have r₁ := b3e142 X0 X0 X0
             have r₂ := b3e15 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b3e142 X1 X1 X2
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e142 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142
        have b3e187 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 (M.op X1 X1)) = (M.op (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e127 X0 X1
             have i₂ := b3e34 X1 X1 X0
             grind)
          | exact superpose b3e34 b3e127
          | (have j0 := b3e127 X0 X1
             grind)
          | exact resolve b3e127 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127
        have b3e197 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e165 X0 X1
             have i₂ := b3e76 X1
             grind)
          | exact superpose b3e76 b3e165
          | (have j0 := b3e165 X0 X1
             grind)
          | exact resolve b3e165 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e165
        have b3e198 : ∀ X0 : G, (M.op x X0) = (k X0 y) ∨ (M.op X0 X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e166 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e166
          | (have j0 := b3e166 X0
             grind)
          | exact resolve b3e166 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e166
        have b3e201 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e169 X0 X1 X2
             have i₂ := b3e12 X0 X2 X0
             grind)
          | exact superpose b3e12 b3e169
          | (have j0 := b3e169 X0 X1 X2
             grind)
          | exact resolve b3e169 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e169
        have b3e207 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e187 X0 X1
             have i₂ := b3e34 X1 X1 X0
             grind)
          | exact superpose b3e34 b3e187
          | (have j0 := b3e187 X0 X1
             grind)
          | exact resolve b3e187 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187
        have b3e221 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e207 X0 X1
             have j1 := b3e67 X0 X1
             grind)
          | (have r₁ := b3e207 X1 X1
             have r₂ := b3e67 X1 X1
             grind)
          | (have r₁ := b3e207 X0 X1
             have r₂ := b3e67 X0 X1
             grind)
          | exact resolve b3e207 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e207
        have b3e245 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e34 X1 X2 X0
             have i₂ := b3e17 X0 (M.op X1 X2)
             grind)
          | (have i₁ := b3e34 X0 X2 (M.op X0 X2)
             have i₂ := b3e17 (M.op X0 X2) X1
             grind)
          | exact superpose b3e17 b3e34
          | (have j1 := b3e17 X0 (M.op X1 X2)
             grind)
          | exact resolve b3e34 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e252 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 (M.op X0 X2)
             have i₂ := b3e34 X0 X2 X1
             grind)
          | exact superpose b3e34 b3e16
          | (have j0 := b3e16 X1 (M.op X0 X2)
             grind)
          | (have r₁ := b3e16 (M.op X0 X2) X0
             have r₂ := b3e34 X0 X2 (M.op X0 X2)
             grind)
          | (have r₁ := b3e16 x (M.op x X2)
             have r₂ := b3e34 x X2 x
             grind)
          | exact resolve b3e16 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e259 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e33 (M.op X0 X1) X2
             have i₂ := b3e34 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b3e34 b3e33
          | exact resolve b3e33 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e271 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op (M.op X1 X2) X0) = (k X0 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e245 X0 X1 X2
             have j1 := b3e15 X0 (M.op X1 X2)
             grind)
          | (have r₁ := b3e245 X1 X1 X2
             have r₂ := b3e15 X1 X1
             grind)
          | (have r₁ := b3e245 (M.op X1 X2) X1 X2
             have r₂ := b3e15 (M.op X1 X2) (M.op X1 X2)
             grind)
          | (have r₁ := b3e245 X0 X1 X2
             have r₂ := b3e15 X0 (M.op X1 X2)
             grind)
          | exact resolve b3e245 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e245
        have b3e282 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (M.op X1 X2)) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e271 X0 X1 X2
             have i₂ := b3e34 X1 X2 X0
             grind)
          | exact superpose b3e34 b3e271
          | (have j0 := b3e271 X0 X1 X2
             grind)
          | exact resolve b3e271 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e271
        have b3e292 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k X0 (τ X1))
             have i₂ := b3e25 X1 X0
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e360 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
          intro X0
          first
          | (have i₁ := b3e34 (σ y) (σ x) X0
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e34
          | exact resolve b3e34 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e364 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x y)) X0) := by
          intro X0
          first
          | (have i₁ := b3e360 X0
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e360
          | exact resolve b3e360 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e360
        have b3e366 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X1 (τ X0)
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e29
          | exact resolve b3e29 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e469 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e23
          | exact resolve b3e23 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e478 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (σ X0) X1
             have i₂ := b3e76 X0
             grind)
          | exact superpose b3e76 b3e33
          | exact resolve b3e33 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e493 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e164 (M.op X0 X2) X1
             have i₂ := b3e34 X0 X2 X1
             grind)
          | exact superpose b3e34 b3e164
          | (have j0 := b3e164 (M.op X0 X2) X1
             grind)
          | exact resolve b3e164 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e511 : ∀ X0 : G, (M.op x X0) ≠ (M.op X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e164 X0 y
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e164
          | exact resolve b3e164 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e555 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e171 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e567 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e13 (M.op (τ X0) (τ X0))
             have i₂ := b3e78 X0
             grind)
          | exact superpose b3e78 b3e13
          | exact resolve b3e13 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e611 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e16 X1 X2
             have i₂ := b3e201 X2 X0 X1
             grind)
          | (have i₁ := b3e16 X2 X1
             have i₂ := b3e201 X0 X1 X2
             grind)
          | exact superpose b3e201 b3e16
          | (have j0 := b3e16 X1 X2
             have j1 := b3e201 X2 X0 X2
             grind)
          | (have r₁ := b3e16 X2 X1
             have r₂ := b3e201 X2 X1 X2
             grind)
          | (have r₁ := b3e16 X2 X0
             have r₂ := b3e201 X0 X2 X2
             grind)
          | exact resolve b3e16 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e615 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e163 X2 X0
             have i₂ := b3e201 X0 X1 X2
             grind)
          | (have i₁ := b3e163 X2 X1
             have i₂ := b3e201 X0 X1 X2
             grind)
          | exact superpose b3e201 b3e163
          | (have j0 := b3e163 X2 X0
             have j1 := b3e201 X0 X1 X1
             grind)
          | exact resolve b3e163 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e649 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e33 X1 X2
             have i₂ := b3e201 X0 X1 X1
             grind)
          | (have i₁ := b3e33 X2 X1
             have i₂ := b3e201 X2 X1 X2
             grind)
          | exact superpose b3e201 b3e33
          | (have j1 := b3e201 X0 X1 X2
             grind)
          | exact resolve b3e33 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e655 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e23
             have i₂ := b3e201 X0 (σ x) (σ x)
             grind)
          | (have i₁ := b3e23
             have i₂ := b3e201 (σ x) x (σ x)
             grind)
          | exact superpose b3e201 b3e23
          | (have j1 := b3e201 X0 (σ x) x
             grind)
          | exact resolve b3e23 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e660 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x X1) ∨ (M.op y X0) = (k X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e35 X1
             have i₂ := b3e201 X0 y X1
             grind)
          | (have i₁ := b3e35 x
             have i₂ := b3e201 y X1 x
             grind)
          | exact superpose b3e201 b3e35
          | (have j1 := b3e201 X0 x X1
             grind)
          | exact resolve b3e35 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e666 : ∀ X0 X1 : G, (M.op x X0) = (k X0 y) ∨ (M.op X0 X1) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e660 X0 X1
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e660
          | (have j0 := b3e660 X0 X1
             grind)
          | exact resolve b3e660 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e660
        have b3e736 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e68 X0 X0
             have i₂ := b3e163 X0 X1
             grind)
          | (have i₁ := b3e68 X1 X0
             have i₂ := b3e163 X0 X1
             grind)
          | exact superpose b3e163 b3e68
          | (have j1 := b3e163 X1 X0
             grind)
          | (have r₁ := b3e68 X1 X1
             have r₂ := b3e163 X1 X1
             grind)
          | (have r₁ := b3e68 X0 X0
             have r₂ := b3e163 X0 X0
             grind)
          | exact resolve b3e68 b3e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e741 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b3e68 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | (have j0 := b3e68 (σ x) (σ x)
             grind)
          | (have r₁ := b3e68 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e757 : (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by grind
        clear b3e741
        have b3e760 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e736 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e736
        have b3e770 : (M.op (σ y) (σ x)) = (k (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b3e757
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e757
          | exact resolve b3e757 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e757
        have b3e781 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b3e770
             have i₂ := b3e18 (M.op x x) y
             grind)
          | exact superpose b3e18 b3e770
          | exact resolve b3e770 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e770
        have b3e786 : (σ (k x y)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b3e781
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e781
          | exact resolve b3e781 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e781
        have b3e790 : (σ (M.op x y)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b3e786
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e786
          | exact resolve b3e786 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e786
        have b3e827 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e172 (M.op X0 x)
             have i₂ := b3e34 X0 x (σ x)
             grind)
          | exact superpose b3e34 b3e172
          | (have j0 := b3e172 X0
             grind)
          | exact resolve b3e172 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e971 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = (M.op X1 (τ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (τ X0) X1
             have i₂ := b3e567 X0
             grind)
          | exact superpose b3e567 b3e33
          | exact resolve b3e33 b3e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e567
        have b3e1055 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ y) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e76 (M.op x y)
             have i₂ := b3e364 (σ (M.op x y))
             grind)
          | exact superpose b3e364 b3e76
          | exact resolve b3e76 b3e364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1085 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e172 (σ (M.op x y))
             have i₂ := b3e364 (σ x)
             grind)
          | exact superpose b3e364 b3e172
          | (have j0 := b3e172 (σ y)
             grind)
          | exact resolve b3e172 b3e364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e172 b3e364
        have b3e1086 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e1085
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e1085
          | exact resolve b3e1085 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1085
        have b3e1101 : (M.op (σ y) (σ (M.op x y))) = (σ (M.op x (M.op x y))) := by
          first
          | (have i₁ := b3e1055
             have i₂ := b3e34 x y (M.op x y)
             grind)
          | exact superpose b3e34 b3e1055
          | exact resolve b3e1055 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1055
        have b3e1108 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e1086
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e1086
          | exact resolve b3e1086 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1086
        have b3e1109 : (M.op (σ y) (σ x)) = (k (σ x) (σ (M.op x y))) := by grind
        clear b3e1108
        have b3e1114 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e1101
             have i₂ := b3e38 x
             grind)
          | exact superpose b3e38 b3e1101
          | exact resolve b3e1101 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1101
        have b3e1117 : (M.op (σ y) (σ x)) = (σ (k x (M.op x y))) := by
          first
          | (have i₁ := b3e1109
             have i₂ := b3e18 x (M.op x y)
             grind)
          | exact superpose b3e18 b3e1109
          | exact resolve b3e1109 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1109
        have b3e1120 : (σ (k x y)) = (σ (k x (M.op x y))) := by
          first
          | (have i₁ := b3e1117
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e1117
          | exact resolve b3e1117 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1117
        have b3e1122 : (σ (M.op x y)) = (σ (k x (M.op x y))) := by
          first
          | (have i₁ := b3e1120
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e1120
          | exact resolve b3e1120 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1120
        have b3e1506 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) (σ (k x y))) ∨ (k (σ (k x y)) (M.op X0 X0)) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e70 (σ y) x (σ x)
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e70
          | exact resolve b3e70 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e70
        have b3e1535 : ∀ X0 : G, (M.op (σ y) X0) ≠ (M.op (σ y) (σ (M.op x y))) ∨ (k (σ (k x y)) (M.op X0 X0)) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e1506 X0
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e1506
          | (have j0 := b3e1506 X0
             grind)
          | exact resolve b3e1506 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1506
        have b3e1554 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (k (σ (k x y)) (M.op X0 X0)) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e1535 X0
             have i₂ := b3e1114
             grind)
          | exact superpose b3e1114 b3e1535
          | (have j0 := b3e1535 X0
             grind)
          | exact resolve b3e1535 b3e1114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1114 b3e1535
        have b3e1570 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 (σ (M.op x y))) = (k (σ (M.op x y)) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1554 X0
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e1554
          | (have j0 := b3e1554 X0
             grind)
          | exact resolve b3e1554 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88 b3e1554
        have b3e1785 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e101 X0 X1
             have i₂ := b3e163 X0 X1
             grind)
          | (have i₁ := b3e101 X0 X0
             have i₂ := b3e163 X0 X1
             grind)
          | exact superpose b3e163 b3e101
          | (have j0 := b3e101 X0 X1
             have j1 := b3e163 X0 X1
             grind)
          | (have r₁ := b3e101 X0 X1
             have r₂ := b3e163 X0 X1
             grind)
          | (have r₁ := b3e101 X0 X0
             have r₂ := b3e163 X0 X0
             grind)
          | exact resolve b3e101 b3e163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e163
        have b3e1786 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e101 X1 X2
             have i₂ := b3e201 X2 X0 X1
             grind)
          | (have i₁ := b3e101 X2 X1
             have i₂ := b3e201 X0 X1 X2
             grind)
          | exact superpose b3e201 b3e101
          | (have j0 := b3e101 X1 X2
             have j1 := b3e201 X2 X0 X2
             grind)
          | (have r₁ := b3e101 X2 X1
             have r₂ := b3e201 X2 X1 X2
             grind)
          | (have r₁ := b3e101 X2 X0
             have r₂ := b3e201 X0 X2 X2
             grind)
          | exact resolve b3e101 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e101
        have b3e1799 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e1785 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1785
        have b3e1806 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e1799 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e1799 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e1799 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e1799 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1799
        have b3e1877 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b3e478 y X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e478
          | exact resolve b3e478 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2302 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 X1))) = (M.op X2 (τ (M.op X0 (M.op X0 X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e971 (M.op X0 X1) X2
             have i₂ := b3e34 X0 X1 (M.op X0 X1)
             grind)
          | exact superpose b3e34 b3e971
          | exact resolve b3e971 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e971
        have b3e2581 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e103 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e103
        have b3e3220 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e197 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197
        have b3e6060 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) = (k (M.op X0 X2) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e555 (M.op X0 X2) x
             have i₂ := b3e34 X0 X2 x
             grind)
          | exact superpose b3e34 b3e555
          | exact resolve b3e555 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6074 : ∀ X0 : G, (M.op x X0) ≠ (M.op X0 y) ∨ (M.op x X0) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e555 y X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e555
          | exact resolve b3e555 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6082 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e555 X1 X2
             have i₂ := b3e201 X2 X0 X1
             grind)
          | (have i₁ := b3e555 X2 X1
             have i₂ := b3e201 X0 X1 X2
             grind)
          | exact superpose b3e201 b3e555
          | (have j0 := b3e555 X1 X2
             have j1 := b3e201 X2 X0 X2
             grind)
          | (have r₁ := b3e555 X1 X1
             have r₂ := b3e201 X1 X1 X1
             grind)
          | (have r₁ := b3e555 X0 X0
             have r₂ := b3e201 X0 X0 X0
             grind)
          | exact resolve b3e555 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6086 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X1) X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e555 (M.op X1 X1) X0
             have i₂ := b3e33 X1 X0
             grind)
          | exact superpose b3e33 b3e555
          | (have j0 := b3e555 (M.op X1 X1) X0
             grind)
          | exact resolve b3e555 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6088 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) X0) ∨ (M.op (M.op x y) X0) = (k (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b3e555 (M.op x y) X0
             have i₂ := b3e38 X0
             grind)
          | exact superpose b3e38 b3e555
          | (have j0 := b3e555 (M.op x y) X0
             grind)
          | exact resolve b3e555 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6095 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e555 X1 (M.op X0 X2)
             have i₂ := b3e34 X0 X2 X1
             grind)
          | exact superpose b3e34 b3e555
          | (have j0 := b3e555 X1 (M.op X0 X2)
             grind)
          | exact resolve b3e555 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6109 : ∀ X0 : G, (M.op x X0) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e555 X0 y
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e555
          | (have j0 := b3e555 X0 y
             grind)
          | exact resolve b3e555 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6139 : ∀ X0 : G, (M.op x X0) ≠ (M.op X0 y) ∨ (M.op (M.op x y) X0) = (k (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b3e6088 X0
             have i₂ := b3e34 x y X0
             grind)
          | exact superpose b3e34 b3e6088
          | (have j0 := b3e6088 X0
             grind)
          | exact resolve b3e6088 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6088
        have b3e6141 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e6086 X0 X1
             have i₂ := b3e34 X1 X1 X0
             grind)
          | exact superpose b3e34 b3e6086
          | (have j0 := b3e6086 X0 X1
             grind)
          | (have r₁ := b3e6086 x x
             have r₂ := b3e34 x x x
             grind)
          | exact resolve b3e6086 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6086
        have b3e6179 : ∀ X0 : G, (M.op x X0) ≠ (M.op X0 y) ∨ (M.op x X0) = (k (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b3e6139 X0
             have i₂ := b3e34 x y X0
             grind)
          | exact superpose b3e34 b3e6139
          | (have j0 := b3e6139 X0
             grind)
          | exact resolve b3e6139 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6139
        have b3e6181 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k (M.op X1 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e6141 X0 X1
             have i₂ := b3e34 X1 X1 X0
             grind)
          | exact superpose b3e34 b3e6141
          | (have j0 := b3e6141 X0 X1
             grind)
          | exact resolve b3e6141 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6141
        have b3e7416 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op x X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op x X1) = (k X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e555 X0 X1
             have i₂ := b3e666 X1 X0
             grind)
          | (have i₁ := b3e555 X1 x
             have i₂ := b3e666 X0 X1
             grind)
          | exact superpose b3e666 b3e555
          | (have j0 := b3e555 X0 X1
             have j1 := b3e666 X1 X1
             grind)
          | (have r₁ := b3e555 x x
             have r₂ := b3e666 x x
             grind)
          | exact resolve b3e555 b3e666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e9539 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op x (M.op X0 X1)) ∨ (M.op x (M.op X0 X1)) = (k y (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e6074 (M.op X0 X1)
             have i₂ := b3e34 X0 X1 y
             grind)
          | exact superpose b3e34 b3e6074
          | (have j0 := b3e6074 (M.op X0 X1)
             grind)
          | exact resolve b3e6074 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6074
        have b3e9701 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e6109 X0
             have i₂ := b3e198 X0
             grind)
          | (have i₁ := b3e6109 x
             have i₂ := b3e198 x
             grind)
          | exact superpose b3e198 b3e6109
          | (have j0 := b3e6109 X0
             have j1 := b3e198 X0
             grind)
          | (have r₁ := b3e6109 y
             have r₂ := b3e198 y
             grind)
          | exact resolve b3e6109 b3e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6109
        have b3e9756 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b3e67 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e67
          | (have j0 := b3e67 (σ x) (σ x)
             grind)
          | (have r₁ := b3e67 (σ x) (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e67 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e9814 : (M.op (σ y) (σ x)) = (k (σ x) (M.op (σ y) (σ y))) := by grind
        clear b3e9756
        have b3e9856 : (M.op (σ y) (σ x)) = (k (σ x) (σ (M.op y y))) := by
          first
          | (have i₁ := b3e9814
             have i₂ := b3e76 y
             grind)
          | exact superpose b3e76 b3e9814
          | exact resolve b3e9814 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9814
        have b3e9903 : (M.op (σ y) (σ x)) = (σ (k x (M.op y y))) := by
          first
          | (have i₁ := b3e9856
             have i₂ := b3e18 x (M.op y y)
             grind)
          | exact superpose b3e18 b3e9856
          | exact resolve b3e9856 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9856
        have b3e9945 : (M.op (σ y) (σ x)) = (σ (k x (M.op x y))) := by
          first
          | (have i₁ := b3e9903
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e9903
          | exact resolve b3e9903 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9903
        have b3e9979 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e9945
             have i₂ := b3e1122
             grind)
          | exact superpose b3e1122 b3e9945
          | exact resolve b3e9945 b3e1122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1122 b3e9945
        have b3e10221 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e176 (M.op X0 X2) X3 X2
             have i₂ := b3e34 X0 X2 X3
             grind)
          | exact superpose b3e34 b3e176
          | (have j0 := b3e176 X0 X1 X2
             grind)
          | exact resolve b3e176 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e176
        have b3e10933 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e68 X0 X0
             have i₂ := b3e221 X0 X1
             grind)
          | (have i₁ := b3e68 X1 X0
             have i₂ := b3e221 X0 X1
             grind)
          | exact superpose b3e221 b3e68
          | (have j1 := b3e221 X1 X0
             grind)
          | (have r₁ := b3e68 X1 X1
             have r₂ := b3e221 X1 X1
             grind)
          | (have r₁ := b3e68 X0 X0
             have r₂ := b3e221 X0 X0
             grind)
          | exact resolve b3e68 b3e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e10985 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e221 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e221 X0 X1
             grind)
          | exact superpose b3e221 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e221 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e221 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e221 X0 X0
             grind)
          | exact resolve b3e16 b3e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e221
        have b3e11052 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e10985 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10985
        have b3e11061 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e10933 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10933
        have b3e11096 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e11052 X0 X1
             have j1 := b3e67 X0 X1
             grind)
          | (have r₁ := b3e11052 X0 X1
             have r₂ := b3e67 X0 X1
             grind)
          | (have r₁ := b3e11052 X1 X1
             have r₂ := b3e67 X1 X1
             grind)
          | exact resolve b3e11052 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11052
        have b3e11696 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e67 X0 X0
             have i₂ := b3e282 X0 X1 X2
             grind)
          | (have i₁ := b3e67 X1 X0
             have i₂ := b3e282 X0 X1 X2
             grind)
          | exact superpose b3e282 b3e67
          | (have j1 := b3e282 X1 X0 X1
             grind)
          | (have r₁ := b3e67 X1 X1
             have r₂ := b3e282 X1 X1 X2
             grind)
          | (have r₁ := b3e67 X0 X0
             have r₂ := b3e282 X0 X0 X2
             grind)
          | exact resolve b3e67 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e11697 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e68 X0 X0
             have i₂ := b3e282 X0 X1 X2
             grind)
          | (have i₁ := b3e68 X1 X0
             have i₂ := b3e282 X0 X1 X2
             grind)
          | exact superpose b3e282 b3e68
          | (have j1 := b3e282 X1 X0 X2
             grind)
          | (have r₁ := b3e68 X1 X1
             have r₂ := b3e282 X1 X1 X2
             grind)
          | (have r₁ := b3e68 X0 X0
             have r₂ := b3e282 X0 X0 X2
             grind)
          | exact resolve b3e68 b3e282
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68 b3e282
        have b3e11825 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e11697 X0 X1 X2
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11697
        have b3e11826 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e11696 X0 X1 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11696
        have b3e13363 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X1 (M.op X0 X3)) = (k (M.op X0 X3) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e649 (M.op X0 X3) X1 X2
             have i₂ := b3e34 X0 X3 X1
             grind)
          | exact superpose b3e34 b3e649
          | (have j0 := b3e649 X0 X1 X2
             grind)
          | exact resolve b3e649 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e649
        have b3e16628 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ x) (M.op X0 X1)) = (k (M.op X0 X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e655 (M.op X0 X1)
             have i₂ := b3e34 X0 X1 (σ x)
             grind)
          | exact superpose b3e34 b3e655
          | (have j0 := b3e655 X0
             grind)
          | exact resolve b3e655 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e655
        have b3e33657 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e827 (σ y) x
             have i₂ := b3e9979
             grind)
          | exact superpose b3e9979 b3e827
          | (have r₁ := b3e827 (σ y) x
             have r₂ := b3e9979
             grind)
          | exact resolve b3e827 b3e9979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e827
        have b3e33683 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (M.op (σ y) X0)) := by
          intro X0
          first
          | (have j0 := b3e33657 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33657
        have b3e33771 : ∀ X0 : G, (τ (σ (M.op x y))) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e292 x (M.op (σ y) X0)
             have i₂ := b3e33683 X0
             grind)
          | exact superpose b3e33683 b3e292
          | exact resolve b3e292 b3e33683
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33683
        have b3e33789 : ∀ X0 : G, (M.op x y) = (k x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e33771 X0
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e33771
          | exact resolve b3e33771 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33771
        have b3e33881 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e85 X0
             have i₂ := b3e198 X0
             grind)
          | (have i₁ := b3e85 x
             have i₂ := b3e198 x
             grind)
          | exact superpose b3e198 b3e85
          | (have j0 := b3e85 X0
             have j1 := b3e198 X0
             grind)
          | (have r₁ := b3e85 X0
             have r₂ := b3e198 X0
             grind)
          | (have r₁ := b3e85 x
             have r₂ := b3e198 x
             grind)
          | exact resolve b3e85 b3e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85 b3e198
        have b3e33897 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e33881 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33881
        have b3e33906 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e33897 X0
             have j1 := b3e9701 X0
             grind)
          | (have r₁ := b3e33897 X0
             have r₂ := b3e9701 X0
             grind)
          | (have r₁ := b3e33897 y
             have r₂ := b3e9701 y
             grind)
          | exact resolve b3e33897 b3e9701
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9701 b3e33897
        have b3e42391 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ y) X0) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e615 (σ x) (σ y) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e615
          | (have j0 := b3e615 (σ x) X0 (σ x)
             grind)
          | exact resolve b3e615 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e615
        have b3e43468 : ∀ X0 : G, (σ (M.op x x)) = (k (σ y) X0) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e42391 X0
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e42391
          | (have j0 := b3e42391 X0
             grind)
          | exact resolve b3e42391 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42391
        have b3e43745 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x x)) = (k (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e43468 X0
             have i₂ := b3e76 y
             grind)
          | exact superpose b3e76 b3e43468
          | (have j0 := b3e43468 X0
             grind)
          | exact resolve b3e43468 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43468
        have b3e43920 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (k (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e43745 X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e43745
          | (have j0 := b3e43745 X0
             grind)
          | exact resolve b3e43745 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43745
        have b3e44055 : ∀ X0 : G, (σ (M.op x x)) = (k (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) := by
          intro X0
          first
          | (have j0 := b3e43920 X0
             grind)
          | (have r₁ := b3e43920 X0
             have r₂ := b3e23
             grind)
          | exact resolve b3e43920 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e43920
        have b3e49917 : ∀ X0 X1 : G, (M.op X0 y) ≠ (M.op x (M.op X0 X1)) ∨ (k (M.op x y) (M.op X0 X1)) = (M.op x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e6179 (M.op X0 X1)
             have i₂ := b3e34 X0 X1 y
             grind)
          | exact superpose b3e34 b3e6179
          | (have j0 := b3e6179 (M.op X0 X1)
             grind)
          | exact resolve b3e6179 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6179
        have b3e51798 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = (k (M.op X1 X1) X2) ∨ (M.op X0 X2) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e6181 X2 X1
             have i₂ := b3e201 X2 X0 X1
             grind)
          | (have i₁ := b3e6181 X1 X2
             have i₂ := b3e201 X0 X1 X2
             grind)
          | exact superpose b3e201 b3e6181
          | (have j0 := b3e6181 X2 X1
             have j1 := b3e201 X2 X0 X2
             grind)
          | (have r₁ := b3e6181 X1 X1
             have r₂ := b3e201 X1 X1 X1
             grind)
          | (have r₁ := b3e6181 X0 X0
             have r₂ := b3e201 X0 X0 X0
             grind)
          | exact resolve b3e6181 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6181
        have b3e57833 : ∀ X0 : G, (M.op y (M.op x X0)) = (k (M.op y y) (M.op x X0)) ∨ (M.op y y) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e2581 y X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e2581
          | exact resolve b3e2581 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2581
        have b3e57978 : ∀ X0 : G, (M.op y (M.op x X0)) = (k (M.op x y) (M.op x X0)) ∨ (M.op y y) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e57833 X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e57833
          | (have j0 := b3e57833 X0
             grind)
          | exact resolve b3e57833 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57833
        have b3e58110 : ∀ X0 : G, (M.op x (M.op x X0)) = (k (M.op x y) (M.op x X0)) ∨ (M.op y y) = (M.op y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e57978 X0
             have i₂ := b3e35 (M.op x X0)
             grind)
          | exact superpose b3e35 b3e57978
          | (have j0 := b3e57978 X0
             grind)
          | exact resolve b3e57978 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57978
        have b3e58228 : ∀ X0 : G, (M.op y y) = (M.op x (M.op x X0)) ∨ (M.op x (M.op x X0)) = (k (M.op x y) (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e58110 X0
             have i₂ := b3e35 (M.op x X0)
             grind)
          | exact superpose b3e35 b3e58110
          | (have j0 := b3e58110 X0
             grind)
          | exact resolve b3e58110 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58110
        have b3e58309 : ∀ X0 : G, (M.op x y) = (M.op x (M.op x X0)) ∨ (M.op x (M.op x X0)) = (k (M.op x y) (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e58228 X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e58228
          | (have j0 := b3e58228 X0
             grind)
          | exact resolve b3e58228 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58228
        have b3e58374 : ∀ X0 : G, (M.op x (M.op x X0)) = (k (M.op x y) (M.op x X0)) := by
          intro X0
          first
          | (have j0 := b3e58309 X0
             have j1 := b3e49917 x X0
             grind)
          | (have r₁ := b3e58309 x
             have r₂ := b3e49917 x x
             grind)
          | exact resolve b3e58309 b3e49917
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49917 b3e58309
        have b3e71833 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e1570 (σ x)
             have i₂ := b3e9979
             grind)
          | exact superpose b3e9979 b3e1570
          | (have j0 := b3e1570 (σ x)
             grind)
          | (have r₁ := b3e1570 (σ x)
             have r₂ := b3e9979
             grind)
          | exact resolve b3e1570 b3e9979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1570
        have b3e71914 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (M.op (σ x) (σ x))) := by grind
        clear b3e71833
        have b3e71989 : (M.op (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x x))) := by
          first
          | (have i₁ := b3e71914
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e71914
          | exact resolve b3e71914 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71914
        have b3e72029 : (M.op (σ x) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x x))) := by
          first
          | (have i₁ := b3e71989
             have i₂ := b3e18 (M.op x y) (M.op x x)
             grind)
          | exact superpose b3e18 b3e71989
          | exact resolve b3e71989 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71989
        have b3e72062 : (σ (M.op x (M.op x x))) = (M.op (σ x) (σ (M.op x y))) := by
          first
          | (have i₁ := b3e72029
             have i₂ := b3e58374 x
             grind)
          | exact superpose b3e58374 b3e72029
          | exact resolve b3e72029 b3e58374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58374 b3e72029
        have b3e72082 : (M.op (σ x) (σ y)) = (σ (M.op x (M.op x x))) := by
          first
          | (have i₁ := b3e72062
             have i₂ := b3e1877 (σ x)
             grind)
          | exact superpose b3e1877 b3e72062
          | exact resolve b3e72062 b3e1877
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72062
        have b3e72099 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e72082
             have i₂ := b3e33 x x
             grind)
          | exact superpose b3e33 b3e72082
          | exact resolve b3e72082 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72082
        have b3e95176 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) ∨ (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e252 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e252
        have b3e95215 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e95176 X0 X1
             have j1 := b3e6095 X0 X0 X1
             grind)
          | (have r₁ := b3e95176 X1 x
             have r₂ := b3e6095 X1 X1 x
             grind)
          | exact resolve b3e95176 b3e6095
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6095 b3e95176
        have b3e95888 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 X1)) = (k (M.op X0 X2) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e95215 (M.op X0 X2) x
             have i₂ := b3e34 X0 X2 x
             grind)
          | exact superpose b3e34 b3e95215
          | exact resolve b3e95215 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e95938 : ∀ X0 : G, (M.op y (M.op x X0)) = (k y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e95215 y X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e95215
          | exact resolve b3e95215 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e96056 : ∀ X0 X1 : G, (τ (M.op (σ X0) (M.op (σ X0) X1))) = (k X0 (τ (M.op (σ X0) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e292 X0 (M.op (σ X0) X1)
             have i₂ := b3e95215 (σ X0) X1
             grind)
          | exact superpose b3e95215 b3e292
          | exact resolve b3e292 b3e95215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95215
        have b3e96132 : ∀ X0 : G, (M.op x (M.op x X0)) = (k y (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e95938 X0
             have i₂ := b3e35 (M.op x X0)
             grind)
          | exact superpose b3e35 b3e95938
          | exact resolve b3e95938 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95938
        have b3e96164 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X2) (M.op X0 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e95888 X0 X1 X2
             have i₂ := b3e34 X0 X2 (M.op X0 X1)
             grind)
          | exact superpose b3e34 b3e95888
          | exact resolve b3e95888 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95888
        have b3e97835 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X0)) ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e11096 (M.op X0 X1) X0
             have i₂ := b3e96164 X0 X0 X1
             grind)
          | exact superpose b3e96164 b3e11096
          | (have j0 := b3e11096 (M.op X0 X1) X0
             grind)
          | exact resolve b3e11096 b3e96164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11096 b3e96164
        have b3e97906 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 (M.op X0 X1)) ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e97835 X0 X1
             have i₂ := b3e33 X0 X0
             grind)
          | exact superpose b3e33 b3e97835
          | (have j0 := b3e97835 X0 X1
             grind)
          | exact resolve b3e97835 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97835
        have b3e98022 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e97906 X0 X1
             have i₂ := b3e34 X0 X1 X0
             grind)
          | exact superpose b3e34 b3e97906
          | (have j0 := b3e97906 X0 X1
             grind)
          | exact resolve b3e97906 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97906
        have b3e98112 : ∀ X0 X1 : G, (M.op X0 X0) = (k (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have j0 := b3e98022 X0 X1
             have j1 := b3e6060 X0 X0 X1
             grind)
          | (have r₁ := b3e98022 X1 x
             have r₂ := b3e6060 X1 X1 x
             grind)
          | exact resolve b3e98022 b3e6060
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6060 b3e98022
        have b3e98249 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op x X0) X1) ∨ (M.op x X1) = (k X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e98112 X1 X0
             have i₂ := b3e666 X1 X0
             grind)
          | (have i₁ := b3e98112 x X1
             have i₂ := b3e666 X0 X1
             grind)
          | exact superpose b3e666 b3e98112
          | (have j1 := b3e666 X1 X1
             grind)
          | exact resolve b3e98112 b3e666
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e666
        have b3e98433 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 (M.op (σ X0) X1) X0
             have i₂ := b3e98112 (σ X0) X1
             grind)
          | exact superpose b3e98112 b3e29
          | exact resolve b3e29 b3e98112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98112
        have b3e98474 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e98433 X0 X1
             have i₂ := b3e76 X0
             grind)
          | exact superpose b3e76 b3e98433
          | exact resolve b3e98433 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76 b3e98433
        have b3e98569 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ (M.op (σ X0) X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e98474 X0 X1
             have i₂ := b3e13 (M.op X0 X0)
             grind)
          | exact superpose b3e13 b3e98474
          | exact resolve b3e98474 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98474
        have b3e102516 : ∀ X0 : G, (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e611 y x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e611
          | (have j0 := b3e611 x x X0
             grind)
          | (have r₁ := b3e611 y x x
             have r₂ := b3e21
             grind)
          | exact resolve b3e611 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e102616 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e611 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e611
        have b3e102618 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e102516 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102516
        have b3e102655 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e102616 X0 X1
             have j1 := b3e6082 X0 X0 X1
             grind)
          | (have r₁ := b3e102616 x x
             have r₂ := b3e6082 x x x
             grind)
          | (have r₁ := b3e102616 X0 x
             have r₂ := b3e6082 X0 X0 x
             grind)
          | exact resolve b3e102616 b3e6082
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6082 b3e102616
        have b3e102697 : ∀ X0 : G, (M.op x X0) = (k X0 y) ∨ (M.op x x) = (M.op x X0) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e102618 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e102618
          | (have j0 := b3e102618 X0
             grind)
          | exact resolve b3e102618 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102618
        have b3e102814 : ∀ X0 : G, (M.op x X0) = (k X0 y) ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have j0 := b3e102697 X0
             have j1 := b3e7416 x X0
             grind)
          | (have r₁ := b3e102697 x
             have r₂ := b3e7416 x x
             grind)
          | (have r₁ := b3e102697 x
             have r₂ := b3e7416 x x
             grind)
          | exact resolve b3e102697 b3e7416
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7416 b3e102697
        have b3e110400 : ∀ X0 : G, (M.op y X0) = (M.op X0 y) ∨ (M.op y X0) = (k y X0) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e102655 y X0
             have i₂ := b3e33906 X0
             grind)
          | exact superpose b3e33906 b3e102655
          | (have j0 := b3e102655 y X0
             have j1 := b3e33906 X0
             grind)
          | exact resolve b3e102655 b3e33906
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e110812 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e110400 X0
             have j1 := b3e555 y X0
             grind)
          | (have r₁ := b3e110400 x
             have r₂ := b3e555 y x
             grind)
          | (have r₁ := b3e110400 X0
             have r₂ := b3e555 X0 y
             grind)
          | exact resolve b3e110400 b3e555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e555 b3e110400
        have b3e110926 : ∀ X0 : G, (M.op x X0) = (k y X0) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e110812 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e110812
          | (have j0 := b3e110812 X0
             grind)
          | exact resolve b3e110812 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110812
        have b3e111574 : ∀ X0 : G, (M.op y y) = (M.op x (τ (M.op (σ y) X0))) ∨ (k x (τ (M.op (σ y) X0))) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e98569 y X0
             have i₂ := b3e102814 (τ (M.op (σ y) X0))
             grind)
          | exact superpose b3e102814 b3e98569
          | (have j1 := b3e102814 (τ (M.op (σ y) X0))
             grind)
          | exact resolve b3e98569 b3e102814
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98569 b3e102814
        have b3e111615 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) ∨ (k x (τ (M.op (σ y) X0))) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e111574 X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e111574
          | (have j0 := b3e111574 X0
             grind)
          | exact resolve b3e111574 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111574
        have b3e111640 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) ∨ (M.op x y) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e111615 X0
             have i₂ := b3e33789 X0
             grind)
          | exact superpose b3e33789 b3e111615
          | (have j0 := b3e111615 X0
             grind)
          | exact resolve b3e111615 b3e33789
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33789 b3e111615
        have b3e111641 : ∀ X0 : G, (M.op x y) = (M.op x (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have j0 := b3e111640 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111640
        have b3e115062 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op (τ (M.op (σ y) X0)) y) = (k y (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e61 (τ (M.op (σ y) X0))
             have i₂ := b3e111641 X0
             grind)
          | exact superpose b3e111641 b3e61
          | (have j0 := b3e61 y
             grind)
          | (have r₁ := b3e61 (τ (M.op (σ y) X0))
             have r₂ := b3e111641 X0
             grind)
          | exact resolve b3e61 b3e111641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e115196 : ∀ X0 : G, (M.op (τ (M.op (σ y) X0)) y) = (k y (τ (M.op (σ y) X0))) := by
          intro X0
          first
          | (have j0 := b3e115062 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115062
        have b3e124550 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 X0)) ∨ (M.op x (M.op X0 X0)) = (k y (M.op X0 X0)) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e110926 (M.op X0 X0)
             have i₂ := b3e1806 X0 y
             grind)
          | exact superpose b3e1806 b3e110926
          | (have j0 := b3e110926 (M.op X0 X0)
             have j1 := b3e1806 X0 y
             grind)
          | exact resolve b3e110926 b3e1806
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1806 b3e110926
        have b3e124770 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (k y (M.op X0 X0)) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e124550 X0
             have j1 := b3e9539 X0 X0
             grind)
          | (have r₁ := b3e124550 x
             have r₂ := b3e9539 x x
             grind)
          | exact resolve b3e124550 b3e9539
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9539 b3e124550
        have b3e124846 : ∀ X0 : G, (M.op x X0) = (k y (M.op X0 X0)) ∨ (M.op y X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e124770 X0
             have i₂ := b3e33 X0 x
             grind)
          | exact superpose b3e33 b3e124770
          | (have j0 := b3e124770 X0
             grind)
          | exact resolve b3e124770 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e124770
        have b3e124875 : ∀ X0 : G, (M.op x X0) = (k y (M.op X0 X0)) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e124846 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e124846
          | (have j0 := b3e124846 X0
             grind)
          | exact resolve b3e124846 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e124846
        have b3e143662 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op (σ X0) X1))) = (M.op X2 (k X0 (τ (M.op (σ X0) X1)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e2302 (σ X0) X1 X2
             have i₂ := b3e96056 X0 X1
             grind)
          | exact superpose b3e96056 b3e2302
          | exact resolve b3e2302 b3e96056
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96056
        have b3e146296 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e3220 (τ X0) (τ X1)
             have i₂ := b3e366 X0 X1
             grind)
          | exact superpose b3e366 b3e3220
          | (have j0 := b3e3220 (τ X1) (τ X0)
             grind)
          | exact resolve b3e3220 b3e366
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e366 b3e3220
        have b3e146541 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e146296 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e146296
          | (have j0 := b3e146296 X0 X1
             grind)
          | exact resolve b3e146296 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146296
        have b3e146655 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e146541 X0 X1
             have i₂ := b3e78 X0
             grind)
          | exact superpose b3e78 b3e146541
          | (have j0 := b3e146541 X0 X1
             grind)
          | exact resolve b3e146541 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146541
        have b3e146747 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e146655 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e146655
          | (have j0 := b3e146655 X0 X1
             grind)
          | exact resolve b3e146655 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146655
        have b3e146824 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e146747 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e146747
          | (have j0 := b3e146747 X0 X1
             grind)
          | exact resolve b3e146747 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146747
        have b3e146892 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
          intro X0 X1
          first
          | (have i₁ := b3e146824 X0 X1
             have i₂ := b3e78 X0
             grind)
          | exact superpose b3e78 b3e146824
          | (have j0 := b3e146824 X0 X1
             grind)
          | exact resolve b3e146824 b3e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78 b3e146824
        have b3e146941 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e146892 X0 X1
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e146892
          | (have j0 := b3e146892 X0 X1
             grind)
          | exact resolve b3e146892 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146892
        have b3e146985 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e146941 X0 X1
             have i₂ := b3e14 X1
             grind)
          | exact superpose b3e14 b3e146941
          | (have j0 := b3e146941 X0 X1
             grind)
          | exact resolve b3e146941 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146941
        have b3e147021 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e146985 X0 X1
             have i₂ := b3e14 (k X0 X1)
             grind)
          | exact superpose b3e14 b3e146985
          | (have j0 := b3e146985 X0 X1
             grind)
          | exact resolve b3e146985 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146985
        have b3e147049 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e147021 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e147021 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e147021 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | (have r₁ := b3e147021 X0 X0
             have r₂ := b3e15 X0 X0
             grind)
          | exact resolve b3e147021 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e147021
        have b3e150113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e147049 X0 X1
             have i₂ := b3e102655 X0 X1
             grind)
          | exact superpose b3e102655 b3e147049
          | (have j0 := b3e147049 X1 X0
             have j1 := b3e102655 X0 X1
             grind)
          | (have r₁ := b3e147049 X1 X1
             have r₂ := b3e102655 X1 X1
             grind)
          | exact resolve b3e147049 b3e102655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102655
        have b3e150134 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op y X0) = (M.op X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e147049 X0 y
             have i₂ := b3e33906 X0
             grind)
          | exact superpose b3e33906 b3e147049
          | (have j1 := b3e33906 X0
             grind)
          | (have r₁ := b3e147049 y y
             have r₂ := b3e33906 y
             grind)
          | (have r₁ := b3e147049 x y
             have r₂ := b3e33906 x
             grind)
          | exact resolve b3e147049 b3e33906
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33906 b3e147049
        have b3e150240 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) ∨ (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e150134 X0
             have i₂ := b3e35 X0
             grind)
          | exact superpose b3e35 b3e150134
          | (have j0 := b3e150134 X0
             grind)
          | exact resolve b3e150134 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150134
        have b3e150245 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e150113 X0 X1
             have j1 := b3e164 X1 X0
             grind)
          | (have r₁ := b3e150113 X0 X1
             have r₂ := b3e164 X0 X1
             grind)
          | (have r₁ := b3e150113 X1 X0
             have r₂ := b3e164 X0 X1
             grind)
          | exact resolve b3e150113 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150113
        have b3e150310 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e150240 X0
             have j1 := b3e511 X0
             grind)
          | (have r₁ := b3e150240 X0
             have r₂ := b3e511 X0
             grind)
          | exact resolve b3e150240 b3e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150240
        have b3e156594 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e1786 X0 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1786
        have b3e156637 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e156594 X0 X1
             have j1 := b3e51798 X0 X0 X1
             grind)
          | (have r₁ := b3e156594 x x
             have r₂ := b3e51798 x x x
             grind)
          | (have r₁ := b3e156594 X0 x
             have r₂ := b3e51798 X0 X0 x
             grind)
          | exact resolve b3e156594 b3e51798
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51798 b3e156594
        have b3e233788 : ∀ X0 X1 : G, (M.op X1 y) ≠ (k (M.op x X0) X1) ∨ (M.op x X1) = (k X1 y) ∨ (M.op x X1) = (k X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e150310 X1
             have i₂ := b3e98249 X0 X1
             grind)
          | exact superpose b3e98249 b3e150310
          | (have j0 := b3e150310 X1
             have j1 := b3e98249 X0 X1
             grind)
          | exact resolve b3e150310 b3e98249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e98249 b3e150310
        have b3e234336 : ∀ X0 X1 : G, (M.op X1 y) ≠ (k (M.op x X0) X1) ∨ (M.op x X1) = (k X1 y) := by
          intro X0 X1
          first
          | (have j0 := b3e233788 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e233788
        have b3e318415 : ∀ X0 : G, (M.op x X0) = (M.op X0 y) ∨ (M.op x X0) = (k X0 y) ∨ (M.op X0 y) = (k (M.op X0 y) y) := by
          intro X0
          first
          | (have i₁ := b3e124875 X0
             have i₂ := b3e11061 X0 y
             grind)
          | exact superpose b3e11061 b3e124875
          | (have j0 := b3e124875 X0
             have j1 := b3e11061 X0 y
             grind)
          | exact resolve b3e124875 b3e11061
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11061 b3e124875
        have b3e318424 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 y) y) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b3e318415 X0
             have j1 := b3e511 X0
             grind)
          | (have r₁ := b3e318415 X0
             have r₂ := b3e511 X0
             grind)
          | exact resolve b3e318415 b3e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318415
        have b3e318727 : ∀ X0 : G, (σ (M.op x x)) = (k (σ (M.op x x)) (σ y)) ∨ (σ (M.op x x)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e11825 (σ x) (σ y) x
             have i₂ := b3e72099
             grind)
          | exact superpose b3e72099 b3e11825
          | exact resolve b3e11825 b3e72099
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11825 b3e72099
        have b3e318851 : ∀ X0 : G, (σ (M.op x x)) = (σ (k (M.op x x) y)) ∨ (σ (M.op x x)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e318727 X0
             have i₂ := b3e18 (M.op x x) y
             grind)
          | exact superpose b3e18 b3e318727
          | (have j0 := b3e318727 X0
             grind)
          | exact resolve b3e318727 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318727
        have b3e318863 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ (M.op x x)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e318851 X0
             have i₂ := b3e790
             grind)
          | exact superpose b3e790 b3e318851
          | (have j0 := b3e318851 X0
             grind)
          | exact resolve b3e318851 b3e790
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e790 b3e318851
        have b3e318866 : ∀ X0 : G, (σ (M.op x x)) = (k (σ y) (M.op (σ x) X0)) := by
          intro X0
          first
          | (have j0 := b3e318863 X0
             grind)
          | (have r₁ := b3e318863 X0
             have r₂ := b3e469
             grind)
          | exact resolve b3e318863 b3e469
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318863
        have b3e318967 : ∀ X0 : G, (τ (σ (M.op x x))) = (k y (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b3e292 y (M.op (σ x) X0)
             have i₂ := b3e318866 X0
             grind)
          | exact superpose b3e318866 b3e292
          | exact resolve b3e292 b3e318866
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318866
        have b3e318992 : ∀ X0 : G, (M.op x x) = (k y (τ (M.op (σ x) X0))) := by
          intro X0
          first
          | (have i₁ := b3e318967 X0
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e318967
          | exact resolve b3e318967 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318967
        have b3e319106 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e11826 X1 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11826
        have b3e319107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have j0 := b3e319106 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e319106
        have b3e319205 : ∀ X0 : G, (M.op X0 y) = (k (M.op x y) (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e319107 (M.op x y) X0
             have i₂ := b3e38 X0
             grind)
          | exact superpose b3e38 b3e319107
          | exact resolve b3e319107 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e319227 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X1 X1) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e319107 (M.op X1 X1) (M.op X0 x)
             have i₂ := b3e12 X0 X1 x
             grind)
          | exact superpose b3e12 b3e319107
          | exact resolve b3e319107 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e319107
        have b3e319488 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op X0 y) y) ∨ (k (M.op X0 y) y) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e234336 y (M.op X0 y)
             have i₂ := b3e319205 X0
             grind)
          | exact superpose b3e319205 b3e234336
          | (have j0 := b3e234336 X0 (M.op X0 y)
             grind)
          | exact resolve b3e234336 b3e319205
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e234336 b3e319205
        have b3e319524 : ∀ X0 : G, (k (M.op X0 y) y) = (M.op x (M.op X0 y)) := by
          intro X0
          first
          | (have j0 := b3e319488 X0
             grind)
          | (have r₁ := b3e319488 X0
             have r₂ := b3e34 X0 y y
             grind)
          | exact resolve b3e319488 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e319488
        have b3e319842 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e156637 X1 (M.op X0 X1)
             have i₂ := b3e319227 X0 X1
             grind)
          | exact superpose b3e319227 b3e156637
          | (have j0 := b3e156637 X1 (M.op X0 X1)
             grind)
          | exact resolve b3e156637 b3e319227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e156637 b3e319227
        have b3e319888 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e319842 X0 X1
             have j1 := b3e493 X0 X1 X1
             grind)
          | (have r₁ := b3e319842 X0 x
             have r₂ := b3e493 X0 x x
             grind)
          | exact resolve b3e319842 b3e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e493 b3e319842
        have b3e320543 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e760 X1 X0
             have i₂ := b3e319888 X1 X0
             grind)
          | exact superpose b3e319888 b3e760
          | (have j0 := b3e760 X1 X0
             grind)
          | exact resolve b3e760 b3e319888
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e760
        have b3e320571 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 y)) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e318424 X0
             have i₂ := b3e319888 X0 y
             grind)
          | exact superpose b3e319888 b3e318424
          | (have j0 := b3e318424 X0
             grind)
          | exact resolve b3e318424 b3e319888
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318424 b3e319888
        have b3e320618 : ∀ X0 : G, (M.op X0 y) = (M.op x (M.op X0 y)) ∨ (M.op x X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e320571 X0
             have i₂ := b3e35 (M.op X0 y)
             grind)
          | exact superpose b3e35 b3e320571
          | (have j0 := b3e320571 X0
             grind)
          | exact resolve b3e320571 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320571
        have b3e321835 : ∀ X0 : G, (τ (σ (M.op x x))) = (k (τ (σ y)) X0) ∨ (M.op (σ x) (σ X0)) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e29 (σ y) X0
             have i₂ := b3e44055 (σ X0)
             grind)
          | exact superpose b3e44055 b3e29
          | (have j1 := b3e44055 (σ X0)
             grind)
          | exact resolve b3e29 b3e44055
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44055
        have b3e321846 : ∀ X0 : G, (k y X0) = (τ (σ (M.op x x))) ∨ (M.op (σ x) (σ X0)) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e321835 X0
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e321835
          | (have j0 := b3e321835 X0
             grind)
          | exact resolve b3e321835 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321835
        have b3e321856 : ∀ X0 : G, (M.op x x) = (k y X0) ∨ (M.op (σ x) (σ X0)) = (k (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e321846 X0
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e321846
          | (have j0 := b3e321846 X0
             grind)
          | exact resolve b3e321846 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321846
        have b3e321857 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k X0 x)) ∨ (M.op x x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e321856 X0
             have i₂ := b3e18 X0 x
             grind)
          | exact superpose b3e18 b3e321856
          | (have j0 := b3e321856 X0
             grind)
          | exact resolve b3e321856 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321856
        have b3e334976 : ∀ X0 : G, (M.op x x) = (k y (τ (σ (k X0 x)))) ∨ (M.op x x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e318992 (σ X0)
             have i₂ := b3e321857 X0
             grind)
          | exact superpose b3e321857 b3e318992
          | (have j1 := b3e321857 (τ (σ (k X0 x)))
             grind)
          | exact resolve b3e318992 b3e321857
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321857
        have b3e335074 : ∀ X0 : G, (M.op x x) = (k y (k X0 x)) ∨ (M.op x x) = (k y X0) := by
          intro X0
          first
          | (have i₁ := b3e334976 X0
             have i₂ := b3e13 (k X0 x)
             grind)
          | exact superpose b3e13 b3e334976
          | (have j0 := b3e334976 (k X0 x)
             grind)
          | exact resolve b3e334976 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e334976
        have b3e344122 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ y) X0))) = (M.op X1 (M.op (τ (M.op (σ y) X0)) y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e143662 y X0 X1
             have i₂ := b3e115196 X0
             grind)
          | exact superpose b3e115196 b3e143662
          | exact resolve b3e143662 b3e115196
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115196 b3e143662
        have b3e364104 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e16628 (σ y) X0
             have i₂ := b3e9979
             grind)
          | exact superpose b3e9979 b3e16628
          | (have j0 := b3e16628 (σ y) X0
             grind)
          | (have r₁ := b3e16628 (σ y) x
             have r₂ := b3e9979
             grind)
          | exact resolve b3e16628 b3e9979
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e9979 b3e16628
        have b3e364106 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (k (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have j0 := b3e364104 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364104
        have b3e364232 : ∀ X0 : G, (k (τ (M.op (σ y) X0)) x) = (τ (M.op (σ x) (M.op (σ y) X0))) := by
          intro X0
          first
          | (have i₁ := b3e29 (M.op (σ y) X0) x
             have i₂ := b3e364106 X0
             grind)
          | exact superpose b3e364106 b3e29
          | exact resolve b3e29 b3e364106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364106
        have b3e364367 : ∀ X0 : G, (M.op x x) = (k y (k (τ (M.op (σ y) X0)) x)) := by
          intro X0
          first
          | (have i₁ := b3e318992 (M.op (σ y) X0)
             have i₂ := b3e364232 X0
             grind)
          | exact superpose b3e364232 b3e318992
          | exact resolve b3e318992 b3e364232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e318992 b3e364232
        have b3e364644 : ∀ X0 X1 : G, (M.op x x) = (k y (M.op x (τ (M.op (σ y) X0)))) ∨ (M.op x X1) = (M.op (τ (M.op (σ y) X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e364367 X0
             have i₂ := b3e201 (τ (M.op (σ y) X0)) x X1
             grind)
          | exact superpose b3e201 b3e364367
          | (have j1 := b3e201 x (τ (M.op (σ y) X0)) X1
             grind)
          | exact resolve b3e364367 b3e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e201 b3e364367
        have b3e364655 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op x (τ (M.op (σ y) X0)))) ∨ (M.op x X1) = (M.op (τ (M.op (σ y) X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e364644 X0 X1
             have i₂ := b3e96132 (τ (M.op (σ y) X0))
             grind)
          | exact superpose b3e96132 b3e364644
          | (have j0 := b3e364644 X0 X1
             grind)
          | exact resolve b3e364644 b3e96132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96132 b3e364644
        have b3e364693 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op x y)) ∨ (M.op x X1) = (M.op (τ (M.op (σ y) X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e364655 X0 X1
             have i₂ := b3e111641 X0
             grind)
          | exact superpose b3e111641 b3e364655
          | (have j0 := b3e364655 X0 X1
             grind)
          | exact resolve b3e364655 b3e111641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364655
        have b3e364712 : ∀ X0 X1 : G, (M.op x y) = (M.op x x) ∨ (M.op x X1) = (M.op (τ (M.op (σ y) X0)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e364693 X0 X1
             have i₂ := b3e38 x
             grind)
          | exact superpose b3e38 b3e364693
          | (have j0 := b3e364693 X0 X1
             grind)
          | exact resolve b3e364693 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364693
        have b3e364718 : ∀ X0 X1 : G, (M.op x X1) = (M.op (τ (M.op (σ y) X0)) X1) := by
          intro X0 X1
          first
          | (have j0 := b3e364712 X0 X1
             grind)
          | (have r₁ := b3e364712 X0 X1
             have r₂ := b3e20
             grind)
          | exact resolve b3e364712 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364712
        have b3e365048 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (τ (M.op (σ y) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e344122 X1 X0
             have i₂ := b3e364718 X1 y
             grind)
          | exact superpose b3e364718 b3e344122
          | exact resolve b3e344122 b3e364718
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e344122
        have b3e365053 : ∀ X0 X1 : G, (M.op X1 (σ (τ (M.op (σ y) X0)))) = (M.op X1 (σ (M.op x (τ (M.op (σ y) X0))))) := by
          intro X0 X1
          first
          | (have i₁ := b3e478 (τ (M.op (σ y) X0)) X1
             have i₂ := b3e364718 X0 (τ (M.op (σ y) X0))
             grind)
          | exact superpose b3e364718 b3e478
          | exact resolve b3e478 b3e364718
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e478 b3e364718
        have b3e365471 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op X1 (σ (τ (M.op (σ y) X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e365053 X0 X1
             have i₂ := b3e111641 X0
             grind)
          | exact superpose b3e111641 b3e365053
          | exact resolve b3e365053 b3e111641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111641 b3e365053
        have b3e365475 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (τ (M.op (σ y) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e365048 X0 X1
             have i₂ := b3e38 X0
             grind)
          | exact superpose b3e38 b3e365048
          | exact resolve b3e365048 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38 b3e365048
        have b3e365642 : ∀ X0 X1 : G, (M.op X1 (σ (M.op x y))) = (M.op X1 (M.op (σ y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e365471 X0 X1
             have i₂ := b3e14 (M.op (σ y) X0)
             grind)
          | exact superpose b3e14 b3e365471
          | exact resolve b3e365471 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e365471
        have b3e365691 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X0)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e365642 X0 X1
             have i₂ := b3e1877 X1
             grind)
          | exact superpose b3e1877 b3e365642
          | exact resolve b3e365642 b3e1877
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1877 b3e365642
        have b3e366457 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e320543 X0 (σ y)
             have i₂ := b3e365691 X0 X0
             grind)
          | exact superpose b3e365691 b3e320543
          | (have j0 := b3e320543 X0 (σ y)
             grind)
          | exact resolve b3e320543 b3e365691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320543
        have b3e366480 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (σ y)) ∨ (M.op (σ y) X1) = (k X1 (M.op (σ y) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e10221 (σ y) X1 X0 X2
             have i₂ := b3e365691 X1 X0
             grind)
          | exact superpose b3e365691 b3e10221
          | (have j0 := b3e10221 (σ y) X1 X2 X2
             grind)
          | exact resolve b3e10221 b3e365691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e10221
        have b3e366541 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (k X0 (M.op (σ y) X1)) = (M.op (M.op (σ y) X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 (M.op (σ y) X1)
             have i₂ := b3e365691 X1 X0
             grind)
          | exact superpose b3e365691 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 (σ y) (M.op (σ y) X0)
             have r₂ := b3e365691 X0 (σ y)
             grind)
          | (have r₁ := b3e15 (M.op (σ y) X0) (σ y)
             have r₂ := b3e365691 X0 (M.op (σ y) X0)
             grind)
          | exact resolve b3e15 b3e365691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e366865 : (M.op (σ y) y) = (M.op x (σ y)) ∨ (M.op x (σ y)) = (k (σ y) y) := by
          first
          | (have i₁ := b3e320618 (σ y)
             have i₂ := b3e365691 y x
             grind)
          | exact superpose b3e365691 b3e320618
          | (have j0 := b3e320618 (σ y)
             grind)
          | exact resolve b3e320618 b3e365691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e320618
        have b3e366945 : (M.op x (σ y)) = (k (σ y) y) := by
          first
          | (have j1 := b3e511 (σ y)
             grind)
          | (have r₁ := b3e366865
             have r₂ := b3e511 (σ y)
             grind)
          | exact resolve b3e366865 b3e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e511 b3e366865
        have b3e367059 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k X0 (M.op (σ y) X1)) ∨ (M.op X0 X0) ≠ (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e366541 X0 X1
             have i₂ := b3e34 (σ y) X1 X0
             grind)
          | exact superpose b3e34 b3e366541
          | (have j0 := b3e366541 X0 X1
             grind)
          | exact resolve b3e366541 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e366541
        have b3e367103 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e366457 X0
             have j1 := b3e164 X0 (σ y)
             grind)
          | (have r₁ := b3e366457 x
             have r₂ := b3e164 (σ y) x
             grind)
          | (have r₁ := b3e366457 X0
             have r₂ := b3e164 X0 (σ y)
             grind)
          | exact resolve b3e366457 b3e164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e164 b3e366457
        have b3e367262 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k X0 (M.op (σ y) X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e367059 X0 X1
             have j1 := b3e366480 X0 X0 X1
             grind)
          | (have r₁ := b3e367059 X1 X1
             have r₂ := b3e366480 X1 X1 x
             grind)
          | (have r₁ := b3e367059 (σ y) X1
             have r₂ := b3e366480 (σ y) (σ y) x
             grind)
          | exact resolve b3e367059 b3e366480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e366480 b3e367059
        have b3e368085 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b3e29 X0 y
             have i₂ := b3e367103 X0
             grind)
          | exact superpose b3e367103 b3e29
          | exact resolve b3e29 b3e367103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e368153 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e367103 (σ X0)
             grind)
          | exact superpose b3e367103 b3e18
          | exact resolve b3e18 b3e367103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e367103
        have b3e374495 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (σ (k X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e365691 (σ X0) X1
             have i₂ := b3e368153 X0
             grind)
          | exact superpose b3e368153 b3e365691
          | exact resolve b3e365691 b3e368153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e374821 : ∀ X0 X1 : G, (M.op X1 (τ (σ (k X0 y)))) = (M.op X1 (τ (M.op (σ y) (σ (k X0 y))))) := by
          intro X0 X1
          first
          | (have i₁ := b3e2302 (σ y) (σ X0) x
             have i₂ := b3e368153 X0
             grind)
          | exact superpose b3e368153 b3e2302
          | exact resolve b3e2302 b3e368153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2302
        have b3e374846 : ∀ X0 X1 X2 : G, (k (σ (k X0 y)) X1) = (M.op X1 (σ (k X0 y))) ∨ (M.op X2 X1) = (M.op X2 (M.op (σ y) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e13363 (σ y) X1 X2 (σ X0)
             have i₂ := b3e368153 X0
             grind)
          | exact superpose b3e368153 b3e13363
          | (have j0 := b3e13363 (σ y) X1 X2 x
             grind)
          | exact resolve b3e13363 b3e368153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13363
        have b3e374948 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X2 (σ y)) ∨ (k (σ (k X0 y)) X1) = (M.op X1 (σ (k X0 y))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e374846 X0 X1 X2
             have i₂ := b3e365691 X1 X2
             grind)
          | exact superpose b3e365691 b3e374846
          | (have j0 := b3e374846 X0 X1 X2
             grind)
          | exact resolve b3e374846 b3e365691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e365691 b3e374846
        have b3e374964 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (τ (σ (k X0 y)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e374821 X0 X1
             have i₂ := b3e365475 X1 (σ (k X0 y))
             grind)
          | exact superpose b3e365475 b3e374821
          | exact resolve b3e374821 b3e365475
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e365475 b3e374821
        have b3e375333 : ∀ X0 X1 X2 : G, (M.op X1 (σ y)) = (k (σ (k X0 y)) X1) ∨ (M.op X2 X1) = (M.op X2 (σ y)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e374948 X0 X1 X2
             have i₂ := b3e374495 X0 X1
             grind)
          | exact superpose b3e374495 b3e374948
          | (have j0 := b3e374948 X0 X1 X2
             grind)
          | exact resolve b3e374948 b3e374495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e374948
        have b3e375341 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (k X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e374964 X0 X1
             have i₂ := b3e13 (k X0 y)
             grind)
          | exact superpose b3e13 b3e374964
          | exact resolve b3e374964 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e374964
        have b3e379750 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (M.op x (M.op X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e375341 (M.op X0 y) X1
             have i₂ := b3e319524 X0
             grind)
          | exact superpose b3e319524 b3e375341
          | exact resolve b3e375341 b3e319524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e319524 b3e375341
        have b3e393040 : ∀ X0 X1 : G, (M.op (σ y) X1) = (k X1 (σ (k X0 y))) := by
          intro X0 X1
          first
          | (have i₁ := b3e367262 X1 (σ X0)
             have i₂ := b3e368153 X0
             grind)
          | exact superpose b3e368153 b3e367262
          | exact resolve b3e367262 b3e368153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e368153
        have b3e393318 : ∀ X0 X1 : G, (τ (M.op (σ y) (σ X0))) = (k X0 (τ (M.op (σ y) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e292 X0 (M.op (σ y) X1)
             have i₂ := b3e367262 (σ X0) X1
             grind)
          | exact superpose b3e367262 b3e292
          | exact resolve b3e292 b3e367262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e292 b3e367262
        have b3e393423 : ∀ X0 X1 : G, (τ (M.op (σ y) (σ X0))) = (k X0 (k (τ X1) y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e393318 X0 X1
             have i₂ := b3e368085 X1
             grind)
          | exact superpose b3e368085 b3e393318
          | exact resolve b3e393318 b3e368085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e393318
        have b3e393546 : ∀ X0 X1 : G, (k (τ (σ X0)) y) = (k X0 (k (τ X1) y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e393423 X0 X1
             have i₂ := b3e368085 (σ X0)
             grind)
          | exact superpose b3e368085 b3e393423
          | exact resolve b3e393423 b3e368085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e368085 b3e393423
        have b3e393605 : ∀ X0 X1 : G, (k X0 y) = (k X0 (k (τ X1) y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e393546 X0 X1
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e393546
          | exact resolve b3e393546 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e393546
        have b3e393654 : ∀ X0 X1 : G, (k X1 y) = (k X1 (k X0 y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e393605 X1 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e393605
          | exact resolve b3e393605 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e393605
        have b3e394364 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x (σ y))) := by
          intro X0
          first
          | (have i₁ := b3e393654 (σ y) X0
             have i₂ := b3e366945
             grind)
          | exact superpose b3e366945 b3e393654
          | exact resolve b3e393654 b3e366945
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e366945 b3e393654
        have b3e406900 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k (σ (k X1 y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e150245 X1 (σ (k X0 y))
             have i₂ := b3e374495 X0 X1
             grind)
          | exact superpose b3e374495 b3e150245
          | (have j0 := b3e150245 X0 (σ y)
             grind)
          | (have r₁ := b3e150245 (σ (k X0 y)) (σ y)
             have r₂ := b3e374495 X0 (σ (k X0 y))
             grind)
          | (have r₁ := b3e150245 (σ y) (σ (k X0 y))
             have r₂ := b3e374495 X0 (σ y)
             grind)
          | exact resolve b3e150245 b3e374495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e150245 b3e374495
        have b3e407218 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (k (σ (k X1 y)) X0) := by
          intro X0 X1
          first
          | (have j0 := b3e406900 X0 X1
             have j1 := b3e375333 X1 X0 x
             grind)
          | (have r₁ := b3e406900 X1 X1
             have r₂ := b3e375333 X0 X1 X1
             grind)
          | (have r₁ := b3e406900 (σ y) X1
             have r₂ := b3e375333 X0 (σ y) (σ y)
             grind)
          | exact resolve b3e406900 b3e375333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e375333 b3e406900
        have b3e423397 : ∀ X0 : G, (M.op x x) = (k y (M.op x (σ y))) ∨ (M.op x x) = (k y (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b3e335074 (σ (k X0 y))
             have i₂ := b3e407218 x X0
             grind)
          | exact superpose b3e407218 b3e335074
          | (have j0 := b3e335074 (M.op x (σ y))
             grind)
          | exact resolve b3e335074 b3e407218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e335074 b3e407218
        have b3e423492 : ∀ X0 : G, (M.op x x) = (k y y) ∨ (M.op x x) = (k y (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b3e423397 X0
             have i₂ := b3e394364 y
             grind)
          | exact superpose b3e394364 b3e423397
          | (have j0 := b3e423397 X0
             grind)
          | exact resolve b3e423397 b3e394364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e394364 b3e423397
        have b3e423669 : ∀ X0 : G, (M.op x x) = (M.op y y) ∨ (M.op x x) = (k y (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b3e423492 X0
             have i₂ := b3e59 y
             grind)
          | exact superpose b3e59 b3e423492
          | (have j0 := b3e423492 X0
             grind)
          | exact resolve b3e423492 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e423492
        have b3e423723 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y (σ (k X0 y))) := by
          intro X0
          first
          | (have i₁ := b3e423669 X0
             have i₂ := b3e35 y
             grind)
          | exact superpose b3e35 b3e423669
          | (have j0 := b3e423669 X0
             grind)
          | exact resolve b3e423669 b3e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35 b3e423669
        have b3e423747 : ∀ X0 : G, (M.op x x) = (k y (σ (k X0 y))) := by
          intro X0
          first
          | (have j0 := b3e423723 X0
             grind)
          | (have r₁ := b3e423723 X0
             have r₂ := b3e20
             grind)
          | exact resolve b3e423723 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e423723
        have b3e423754 : (M.op x x) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e423747 x
             have i₂ := b3e393040 x y
             grind)
          | exact superpose b3e393040 b3e423747
          | exact resolve b3e423747 b3e393040
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e393040 b3e423747
        have b3e423947 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e379750 (σ y) X0
             have i₂ := b3e423754
             grind)
          | exact superpose b3e423754 b3e379750
          | exact resolve b3e379750 b3e423754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e379750 b3e423754
        have b3e424293 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b3e423947 X0
             have i₂ := b3e259 x x X0
             grind)
          | exact superpose b3e259 b3e423947
          | exact resolve b3e423947 b3e259
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e259 b3e423947
        have b3e424472 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b3e424293 X0
             have i₂ := b3e33 x X0
             grind)
          | exact superpose b3e33 b3e424293
          | exact resolve b3e424293 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e424293
        have b3e426007 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e469
             have i₂ := b3e424472 x
             grind)
          | exact superpose b3e424472 b3e469
          | exact resolve b3e469 b3e424472
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e469 b3e424472
        have b3e426256 : False := by grind
        exact b3e426256
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : (M.op x x) = (M.op y x) := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e111 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by
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
          have b4e115 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          clear b4e112
          have b4e116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b4e111
          have b4e117 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e115
               have r₂ := b4e21
               grind)
            | exact resolve b4e115 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e118 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e116
               have r₂ := b4e23
               grind)
            | exact resolve b4e116 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e125 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e118
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e118
            | exact resolve b4e118 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118
          have b4e132 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e125
               have i₂ := b4e117
               grind)
            | exact superpose b4e117 b4e125
            | exact resolve b4e125 b4e117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117 b4e125
          have b4e137 : False := by grind
          exact b4e137
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : (M.op x x) = (M.op y x) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e31 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x x) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e13 x X0 x
               grind)
            | exact superpose b5e13 b5e31
            | exact resolve b5e31 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e80 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e94 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e80 (σ X0)
               grind)
            | exact superpose b5e80 b5e19
            | exact resolve b5e19 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e94 X0
               have i₂ := b5e80 X0
               grind)
            | exact superpose b5e80 b5e94
            | exact resolve b5e94 b5e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e80 b5e94
          have b5e180 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e183 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X1
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e193 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e180 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e194 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e193 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e193
          have b5e205 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e183 X0 X1 X2
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e183 X0 (M.op X0 X0) X0
               have r₂ := b5e16 (M.op X0 X0) X0
               grind)
            | (have r₁ := b5e183 X0 (M.op X0 X0) (M.op X0 X0)
               have r₂ := b5e16 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | (have r₁ := b5e183 X0 X1 X2
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e183 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e183
          have b5e208 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e194 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e194 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e194 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e194 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e194
          have b5e243 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e205 X0 X1 X2
               have i₂ := b5e13 X0 X2 X0
               grind)
            | exact superpose b5e13 b5e205
            | (have j0 := b5e205 X0 X1 X2
               grind)
            | exact resolve b5e205 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e205
          have b5e657 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e20
               have i₂ := b5e243 X0 (σ x) (σ y)
               grind)
            | (have i₁ := b5e20
               have i₂ := b5e243 (σ x) x (σ y)
               grind)
            | exact superpose b5e243 b5e20
            | (have j1 := b5e243 X0 (σ x) x
               grind)
            | exact resolve b5e20 b5e243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e243
          have b5e19104 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e657 (σ y)
               have i₂ := b5e97 y
               grind)
            | exact superpose b5e97 b5e657
            | (have j0 := b5e657 (σ y)
               grind)
            | exact resolve b5e657 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e657
          have b5e19132 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b5e19104
               have i₂ := b5e36 y
               grind)
            | exact superpose b5e36 b5e19104
            | exact resolve b5e19104 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e19104
          have b5e19133 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b5e19132
          have b5e19143 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e19133
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e19133
            | exact resolve b5e19133 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19133
          have b5e19782 : (M.op (σ x) (σ x)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e19143
               grind)
            | exact superpose b5e19143 b5e23
            | exact resolve b5e23 b5e19143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e19783 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e19143
               grind)
            | exact superpose b5e19143 b5e20
            | exact resolve b5e20 b5e19143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19143
          have b5e19830 : (σ (M.op x x)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b5e19782
               have i₂ := b5e97 x
               grind)
            | exact superpose b5e97 b5e19782
            | exact resolve b5e19782 b5e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97 b5e19782
          have b5e20564 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e19830
               have i₂ := b5e208 y x
               grind)
            | exact superpose b5e208 b5e19830
            | (have j1 := b5e208 y x
               grind)
            | exact resolve b5e19830 b5e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e208 b5e19830
          have b5e20568 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b5e20564
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e20564
            | exact resolve b5e20564 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20564
          have b5e20569 : (M.op x y) = (k y x) := by grind
          clear b5e20568
          have b5e20625 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e19783
               have i₂ := b5e20569
               grind)
            | exact superpose b5e20569 b5e19783
            | exact resolve b5e19783 b5e20569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19783 b5e20569
          have b5e20626 : False := by grind
          exact b5e20626
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X2) X3 (M.op X1 X1)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 (M.op X0 X0) X2
             have i₂ := b6e12 X0 X0 X0
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e32 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e31 X0 X1 x
             have i₂ := b6e12 X1 X0 x
             grind)
          | exact superpose b6e12 b6e31
          | exact resolve b6e31 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e33 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b6e30 X0 x X2 X3
             have i₂ := b6e12 X0 X3 x
             grind)
          | exact superpose b6e12 b6e30
          | exact resolve b6e30 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b6e62 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (M.op X0 X0) X1
             have i₂ := b6e12 X0 X0 X0
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X0 X0) X1
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e66 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b6e60
        have b6e69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e62 X0 X1
             have i₂ := b6e33 X0 X0 X1
             grind)
          | exact superpose b6e33 b6e62
          | (have j0 := b6e62 X0 X1
             grind)
          | (have r₁ := b6e62 x x
             have r₂ := b6e33 x x x
             grind)
          | exact resolve b6e62 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33 b6e62
        have b6e71 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e66
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e66
          | exact resolve b6e66 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66
        have b6e75 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e69 X0 X1
             have i₂ := b6e32 X0 X1
             grind)
          | exact superpose b6e32 b6e69
          | (have j0 := b6e69 X0 X1
             grind)
          | (have r₁ := b6e69 (M.op X0 X0) X0
             have r₂ := b6e32 X0 (M.op X0 X0)
             grind)
          | (have r₁ := b6e69 X0 (M.op X0 X0)
             have r₂ := b6e32 X0 X0
             grind)
          | exact resolve b6e69 b6e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32 b6e69
        have b6e79 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e65 (σ X0)
             grind)
          | exact superpose b6e65 b6e18
          | exact resolve b6e18 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e79 X0
             have i₂ := b6e65 X0
             grind)
          | exact superpose b6e65 b6e79
          | exact resolve b6e79 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e79
        have b6e141 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e172 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X1 X2 X0
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e12 X0 X1 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 X0 X1
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e180 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e185 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e141 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e186 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e185 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e185
        have b6e187 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e180 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e180 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | (have r₁ := b6e180 X1 X1
             have r₂ := b6e15 X1 X1
             grind)
          | exact resolve b6e180 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e180
        have b6e192 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e172 X0 X1 X2
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e172 X0 (M.op X0 X0) X0
             have r₂ := b6e15 (M.op X0 X0) X0
             grind)
          | (have r₁ := b6e172 X0 (M.op X0 X0) (M.op X0 X0)
             have r₂ := b6e15 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b6e172 X0 X1 X2
             have r₂ := b6e15 X0 X1
             grind)
          | exact resolve b6e172 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e172
        have b6e231 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e192 X0 X1 X2
             have i₂ := b6e12 X0 X2 X0
             grind)
          | exact superpose b6e12 b6e192
          | (have j0 := b6e192 X0 X1 X2
             grind)
          | exact resolve b6e192 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e192
        have b6e354 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e187 (σ y) (σ x)
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e187
          | (have j0 := b6e187 (σ y) (σ x)
             grind)
          | exact resolve b6e187 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e187
        have b6e377 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e354
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e354
          | exact resolve b6e354 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e354
        have b6e383 : (σ (k x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e377
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e377
          | exact resolve b6e377 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e377
        have b6e387 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e383
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e383
          | exact resolve b6e383 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e383
        have b6e388 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e387
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e387
          | exact resolve b6e387 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e387
        have b6e389 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (k x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e388
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e388
          | exact resolve b6e388 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e388
        have b6e396 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e23
          | exact resolve b6e23 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e557 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e75 X0 X0
             have i₂ := b6e186 X0 X1
             grind)
          | (have i₁ := b6e75 X1 X0
             have i₂ := b6e186 X0 X1
             grind)
          | exact superpose b6e186 b6e75
          | (have j1 := b6e186 X1 X0
             grind)
          | (have r₁ := b6e75 X1 X1
             have r₂ := b6e186 X1 X1
             grind)
          | (have r₁ := b6e75 X0 X0
             have r₂ := b6e186 X0 X0
             grind)
          | exact resolve b6e75 b6e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e186
        have b6e568 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by
          first
          | (have i₁ := b6e75 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e75
          | (have j0 := b6e75 (σ x) (σ x)
             grind)
          | (have r₁ := b6e75 (σ x) (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e75 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e581 : (M.op (σ y) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) := by grind
        clear b6e568
        have b6e585 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e557 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e557
        have b6e590 : (M.op (σ y) (σ x)) = (k (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b6e581
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e581
          | exact resolve b6e581 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e581
        have b6e598 : (M.op (σ y) (σ x)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e590
             have i₂ := b6e18 (M.op x x) y
             grind)
          | exact superpose b6e18 b6e590
          | exact resolve b6e590 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e590
        have b6e602 : (σ (k x y)) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b6e598
             have i₂ := b6e71
             grind)
          | exact superpose b6e71 b6e598
          | exact resolve b6e598 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e598
        have b6e8686 : (M.op (σ x) (σ x)) = (k (M.op (σ x) (σ x)) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e585 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e585
          | exact resolve b6e585 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e585
        have b6e8720 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e8686
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e8686
          | exact resolve b6e8686 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8686
        have b6e8724 : (σ (M.op x x)) = (σ (k (M.op x x) y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e8720
             have i₂ := b6e18 (M.op x x) y
             grind)
          | exact superpose b6e18 b6e8720
          | exact resolve b6e8720 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8720
        have b6e8725 : (σ (k x y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e8724
             have i₂ := b6e602
             grind)
          | exact superpose b6e602 b6e8724
          | exact resolve b6e8724 b6e602
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e602 b6e8724
        have b6e8726 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e8725
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e8725
          | exact resolve b6e8725 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8725
        have b6e8727 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e8726
             have i₂ := b6e82 x
             grind)
          | exact superpose b6e82 b6e8726
          | exact resolve b6e8726 b6e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e82 b6e8726
        have b6e8728 : (σ (M.op x x)) = (σ (k y x)) := by
          first
          | (have r₁ := b6e8727
             have r₂ := b6e389
             grind)
          | exact resolve b6e8727 b6e389
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e389 b6e8727
        have b6e8732 : ∀ X0 : G, (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b6e8728
             have i₂ := b6e231 y x X0
             grind)
          | exact superpose b6e231 b6e8728
          | (have j1 := b6e231 x y X0
             grind)
          | exact resolve b6e8728 b6e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e231 b6e8728
        have b6e8785 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have j0 := b6e8732 X0
             grind)
          | (have r₁ := b6e8732 X0
             have r₂ := b6e396
             grind)
          | exact resolve b6e8732 b6e396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e396 b6e8732
        have b6e9493 : (M.op x x) ≠ (M.op x x) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e8785 x
             grind)
          | exact superpose b6e8785 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e8785 x
             grind)
          | exact resolve b6e21 b6e8785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8785
        have b6e9577 : False := by grind
        exact b6e9577
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 (M.op X1 X1)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) X2
               have i₂ := b7e13 X0 X0 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 X0 X1 x
               have i₂ := b7e13 X1 X0 x
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e34 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e31 X0 x X2 X3
               have i₂ := b7e13 X0 X3 x
               grind)
            | exact superpose b7e13 b7e31
            | exact resolve b7e31 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e58 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ x) (σ x)) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e58 X0
               have i₂ := b7e13 (σ x) X0 (σ x)
               grind)
            | exact superpose b7e13 b7e58
            | exact resolve b7e58 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e80 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e80 (σ X0)
               grind)
            | exact superpose b7e80 b7e19
            | exact resolve b7e19 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e94 X0
               have i₂ := b7e80 X0
               grind)
            | exact superpose b7e80 b7e94
            | exact resolve b7e94 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e94
          have b7e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (M.op X1 X1) X1
               have i₂ := b7e13 X1 X1 X1
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 (M.op X0 X0) X1
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e106 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 (M.op X1 X1) (M.op X0 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 (M.op X1 X1) (M.op X0 X2)
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e108 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e110 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e108
          have b7e111 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e110
               have r₂ := b7e23
               grind)
            | exact resolve b7e110 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e113 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e106 X0 X1 X2
               have i₂ := b7e13 X1 X1 X1
               grind)
            | exact superpose b7e13 b7e106
            | (have j0 := b7e106 X0 X1 X2
               grind)
            | (have r₁ := b7e106 X2 X2 X2
               have r₂ := b7e13 X2 X2 X2
               grind)
            | exact resolve b7e106 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) X1) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e102 X0 X1
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e102
            | (have j0 := b7e102 X0 X1
               grind)
            | (have r₁ := b7e102 X0 X0
               have r₂ := b7e33 X0 X0
               grind)
            | exact resolve b7e102 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e118 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e111
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e111
            | exact resolve b7e111 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
          have b7e120 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e113 X0 X1 X2
               have i₂ := b7e13 X1 X1 X1
               grind)
            | exact superpose b7e13 b7e113
            | (have j0 := b7e113 X0 X1 X2
               grind)
            | exact resolve b7e113 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e122 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e115 X0 X1
               have i₂ := b7e34 X0 X0 X1
               grind)
            | exact superpose b7e34 b7e115
            | (have j0 := b7e115 X0 X1
               grind)
            | (have r₁ := b7e115 (M.op X0 x) X0
               have r₂ := b7e34 X0 x (M.op X0 x)
               grind)
            | (have r₁ := b7e115 x (M.op x x)
               have r₂ := b7e34 x x x
               grind)
            | exact resolve b7e115 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e126 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op (M.op X1 X1) (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e120 X0 X1 X2
               have i₂ := b7e34 X1 X1 (M.op X0 X2)
               grind)
            | exact superpose b7e34 b7e120
            | (have j0 := b7e120 X0 X1 X2
               grind)
            | (have r₁ := b7e120 (M.op X0 X2) X0 X2
               have r₂ := b7e34 X0 X2 X0
               grind)
            | (have r₁ := b7e120 X0 (M.op X0 X2) X2
               have r₂ := b7e34 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b7e120 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120
          have b7e128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e122 X0 X1
               have i₂ := b7e34 X0 X0 X1
               grind)
            | exact superpose b7e34 b7e122
            | (have j0 := b7e122 X0 X1
               grind)
            | (have r₁ := b7e122 (M.op X0 x) X0
               have r₂ := b7e34 X0 x (M.op X0 x)
               grind)
            | (have r₁ := b7e122 x (M.op x x)
               have r₂ := b7e34 x x x
               grind)
            | exact resolve b7e122 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122
          have b7e131 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 (M.op X0 X2)) ∨ (M.op X1 (M.op X0 X2)) = (k (M.op X1 X1) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e126 X0 X1 X2
               have i₂ := b7e34 X1 X1 (M.op X0 X2)
               grind)
            | exact superpose b7e34 b7e126
            | (have j0 := b7e126 X0 X1 X2
               grind)
            | (have r₁ := b7e126 (M.op X0 X2) X0 X2
               have r₂ := b7e34 X0 X2 X0
               grind)
            | (have r₁ := b7e126 X0 (M.op X0 X2) X2
               have r₂ := b7e34 X0 X2 (M.op X0 X2)
               grind)
            | exact resolve b7e126 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e126
          have b7e170 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b7e199 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 X0 X1
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e17 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e17
            | (have j0 := b7e17 X0 X1
               have j1 := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X1 X1
               have r₂ := b7e18 X1 X1
               grind)
            | (have r₁ := b7e17 X0 X1
               have r₂ := b7e18 X0 X1
               grind)
            | (have r₁ := b7e17 X0 X0
               have r₂ := b7e18 X0 X0
               grind)
            | exact resolve b7e17 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e212 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e199 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e199
          have b7e213 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e212 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e212
          have b7e216 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e170 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e217 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e216 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e216
          have b7e227 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e213 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e213 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | (have r₁ := b7e213 X1 X1
               have r₂ := b7e16 X1 X1
               grind)
            | exact resolve b7e213 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e213
          have b7e304 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e118
               grind)
            | exact superpose b7e118 b7e23
            | exact resolve b7e23 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e311 : (σ (k x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e304
               have i₂ := b7e97 x
               grind)
            | exact superpose b7e97 b7e304
            | exact resolve b7e304 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e304
          have b7e429 : (σ (M.op x x)) ≠ (σ (M.op y x)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e311
               have i₂ := b7e217 x y
               grind)
            | exact superpose b7e217 b7e311
            | (have j1 := b7e217 x y
               grind)
            | exact resolve b7e311 b7e217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e217 b7e311
          have b7e432 : (σ (M.op x x)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b7e429
               have r₂ := b7e22
               grind)
            | exact resolve b7e429 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e429
          have b7e436 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e26 X1 X0
               have i₂ := b7e227 X0 (τ X1)
               grind)
            | exact superpose b7e227 b7e26
            | (have j1 := b7e227 X0 (τ X1)
               grind)
            | exact resolve b7e26 b7e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e742 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e59 (σ y)
               have i₂ := b7e97 y
               grind)
            | exact superpose b7e97 b7e59
            | exact resolve b7e59 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e757 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 (σ X0) X1
               have i₂ := b7e97 X0
               grind)
            | exact superpose b7e97 b7e33
            | exact resolve b7e33 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1190 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e118
               have i₂ := b7e742
               grind)
            | exact superpose b7e742 b7e118
            | exact resolve b7e118 b7e742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1192 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e20
               have i₂ := b7e742
               grind)
            | exact superpose b7e742 b7e20
            | exact resolve b7e20 b7e742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e742
          have b7e1245 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b7e128 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e128
            | (have j0 := b7e128 (σ x) (σ y)
               grind)
            | (have r₁ := b7e128 (σ x) (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e128 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e1247 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ y)) := by grind
          clear b7e1245
          have b7e1251 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have r₁ := b7e1247
               have r₂ := b7e23
               grind)
            | exact resolve b7e1247 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1247
          have b7e1262 : (M.op (σ x) (σ y)) = (k (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b7e1251
               have i₂ := b7e97 x
               grind)
            | exact superpose b7e97 b7e1251
            | exact resolve b7e1251 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1251
          have b7e1271 : (M.op (σ x) (σ y)) = (σ (k (M.op x x) y)) := by
            first
            | (have i₁ := b7e1262
               have i₂ := b7e19 (M.op x x) y
               grind)
            | exact superpose b7e19 b7e1262
            | exact resolve b7e1262 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1262
          have b7e1277 : (σ (k x y)) = (σ (k (M.op x x) y)) := by
            first
            | (have i₁ := b7e1271
               have i₂ := b7e118
               grind)
            | exact superpose b7e118 b7e1271
            | exact resolve b7e1271 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1271
          have b7e1282 : (σ (M.op y y)) = (σ (k (M.op x x) y)) := by
            first
            | (have i₁ := b7e1277
               have i₂ := b7e1190
               grind)
            | exact superpose b7e1190 b7e1277
            | exact resolve b7e1277 b7e1190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1277
          have b7e1304 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1190
               grind)
            | exact superpose b7e1190 b7e14
            | exact resolve b7e14 b7e1190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1190
          have b7e1305 : (k x y) = (M.op y y) := by
            first
            | (have i₁ := b7e1304
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e1304
            | exact resolve b7e1304 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1304
          have b7e1466 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 X0) (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e131 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131
          have b7e2459 : (σ (M.op y y)) = (σ (M.op (M.op x x) y)) ∨ (k (M.op x x) y) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b7e1282
               have i₂ := b7e227 (M.op x x) y
               grind)
            | exact superpose b7e227 b7e1282
            | (have j1 := b7e227 (M.op x x) y
               grind)
            | exact resolve b7e1282 b7e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e227
          have b7e2463 : (k (M.op x x) y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k (M.op x x) y)
               have i₂ := b7e1282
               grind)
            | exact superpose b7e1282 b7e14
            | exact resolve b7e14 b7e1282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1282
          have b7e2486 : (M.op y y) = (k (M.op x x) y) := by
            first
            | (have i₁ := b7e2463
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e2463
            | exact resolve b7e2463 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2463
          have b7e2490 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (k (M.op x x) y) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b7e2459
               have i₂ := b7e34 x x y
               grind)
            | exact superpose b7e34 b7e2459
            | exact resolve b7e2459 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2459
          have b7e2501 : (k (M.op x x) y) = (M.op y (M.op x x)) := by
            first
            | (have r₁ := b7e2490
               have r₂ := b7e1192
               grind)
            | exact resolve b7e2490 b7e1192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1192 b7e2490
          have b7e2511 : (M.op y x) = (k (M.op x x) y) := by
            first
            | (have i₁ := b7e2501
               have i₂ := b7e33 x y
               grind)
            | exact superpose b7e33 b7e2501
            | exact resolve b7e2501 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2501
          have b7e2921 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e2486
               have i₂ := b7e2511
               grind)
            | exact superpose b7e2511 b7e2486
            | exact resolve b7e2486 b7e2511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2486 b7e2511
          have b7e3189 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b7e33 y X0
               have i₂ := b7e2921
               grind)
            | exact superpose b7e2921 b7e33
            | exact resolve b7e33 b7e2921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e20493 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e436 X0 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e436
            | exact resolve b7e436 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e436
          have b7e20619 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e20493 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e20493
            | (have j0 := b7e20493 X0 X1
               grind)
            | exact resolve b7e20493 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20493
          have b7e57988 : (M.op (σ y) (M.op (σ x) (σ x))) = (k (M.op (σ y) (σ y)) (M.op (σ x) (σ x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e1466 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1466
            | exact resolve b7e1466 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1466
          have b7e58179 : (M.op (σ y) (σ (M.op x x))) = (k (M.op (σ y) (σ y)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e57988
               have i₂ := b7e97 x
               grind)
            | exact superpose b7e97 b7e57988
            | exact resolve b7e57988 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57988
          have b7e58318 : (M.op (σ y) (σ (M.op x x))) = (k (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58179
               have i₂ := b7e59 (σ y)
               grind)
            | exact superpose b7e59 b7e58179
            | exact resolve b7e58179 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58179
          have b7e58436 : (M.op (σ y) (σ (M.op x x))) = (k (σ (k x y)) (σ (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58318
               have i₂ := b7e118
               grind)
            | exact superpose b7e118 b7e58318
            | exact resolve b7e58318 b7e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118 b7e58318
          have b7e58515 : (M.op (σ y) (σ (M.op x x))) = (σ (k (k x y) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58436
               have i₂ := b7e19 (k x y) (M.op x x)
               grind)
            | exact superpose b7e19 b7e58436
            | exact resolve b7e58436 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58436
          have b7e58544 : (M.op (σ y) (σ (M.op x x))) = (σ (k (M.op y y) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58515
               have i₂ := b7e1305
               grind)
            | exact superpose b7e1305 b7e58515
            | exact resolve b7e58515 b7e1305
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1305 b7e58515
          have b7e58567 : (M.op (σ y) (σ (M.op x x))) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58544
               have i₂ := b7e2921
               grind)
            | exact superpose b7e2921 b7e58544
            | exact resolve b7e58544 b7e2921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2921 b7e58544
          have b7e58589 : (M.op (σ x) (σ (M.op x x))) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58567
               have i₂ := b7e59 (σ (M.op x x))
               grind)
            | exact superpose b7e59 b7e58567
            | exact resolve b7e58567 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58567
          have b7e58606 : (M.op (σ x) (σ x)) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58589
               have i₂ := b7e757 x (σ x)
               grind)
            | exact superpose b7e757 b7e58589
            | exact resolve b7e58589 b7e757
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e757 b7e58589
          have b7e58622 : (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b7e58606
               have i₂ := b7e97 x
               grind)
            | exact superpose b7e97 b7e58606
            | exact resolve b7e58606 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e58606
          have b7e58634 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
            first
            | (have i₁ := b7e58622
               have i₂ := b7e59 (M.op (σ x) (σ x))
               grind)
            | exact superpose b7e59 b7e58622
            | exact resolve b7e58622 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58622
          have b7e58646 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
            first
            | (have i₁ := b7e58634
               have i₂ := b7e33 (σ x) (σ x)
               grind)
            | exact superpose b7e33 b7e58634
            | exact resolve b7e58634 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e58634
          have b7e58654 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
            first
            | (have i₁ := b7e58646
               have i₂ := b7e59 (σ y)
               grind)
            | exact superpose b7e59 b7e58646
            | exact resolve b7e58646 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59 b7e58646
          have b7e58661 : (σ (M.op x x)) = (σ (k (M.op y x) (M.op x x))) := by
            first
            | (have r₁ := b7e58654
               have r₂ := b7e23
               grind)
            | exact resolve b7e58654 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58654
          have b7e61010 : (σ (M.op x x)) = (σ (M.op (M.op y x) (M.op x x))) ∨ (k (M.op y x) (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b7e20619 (M.op x x) (M.op y x)
               have i₂ := b7e58661
               grind)
            | exact superpose b7e58661 b7e20619
            | (have j0 := b7e20619 (M.op x x) (M.op y x)
               grind)
            | exact resolve b7e20619 b7e58661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e20619
          have b7e61013 : (k (M.op y x) (M.op x x)) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k (M.op y x) (M.op x x))
               have i₂ := b7e58661
               grind)
            | exact superpose b7e58661 b7e14
            | exact resolve b7e14 b7e58661
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58661
          have b7e61084 : (M.op x x) = (k (M.op y x) (M.op x x)) := by
            first
            | (have i₁ := b7e61013
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e61013
            | exact resolve b7e61013 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61013
          have b7e61087 : (σ (M.op x x)) = (σ (M.op y x)) ∨ (k (M.op y x) (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b7e61010
               have i₂ := b7e13 y x x
               grind)
            | exact superpose b7e13 b7e61010
            | exact resolve b7e61010 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61010
          have b7e61140 : (k (M.op y x) (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have r₁ := b7e61087
               have r₂ := b7e432
               grind)
            | exact resolve b7e61087 b7e432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e432 b7e61087
          have b7e61193 : (M.op x (M.op y x)) = (k (M.op y x) (M.op x x)) := by
            first
            | (have i₁ := b7e61140
               have i₂ := b7e34 x x (M.op y x)
               grind)
            | exact superpose b7e34 b7e61140
            | exact resolve b7e61140 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e61140
          have b7e61237 : (M.op x x) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b7e61193
               have i₂ := b7e61084
               grind)
            | exact superpose b7e61084 b7e61193
            | exact resolve b7e61193 b7e61084
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61084 b7e61193
          have b7e61270 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e61237
               have i₂ := b7e3189 x
               grind)
            | exact superpose b7e3189 b7e61237
            | exact resolve b7e61237 b7e3189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3189 b7e61237
          have b7e61286 : False := by grind
          exact b7e61286
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X1 X1)) := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e71 (σ X0)
               grind)
            | exact superpose b8e71 b8e19
            | exact resolve b8e19 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e83 X0
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e83
            | exact resolve b8e83 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71 b8e83
          have b8e178 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e199 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X2 X2)) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e178 X0 X1 X2
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e178 X0 (M.op X0 X0) X0
               have r₂ := b8e16 (M.op X0 X0) X0
               grind)
            | (have r₁ := b8e178 X0 (M.op X0 X0) (M.op X0 X0)
               have r₂ := b8e16 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | (have r₁ := b8e178 X0 X1 X2
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e178 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e236 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e199 X0 X1 X2
               have i₂ := b8e13 X0 X2 X0
               grind)
            | exact superpose b8e13 b8e199
            | (have j0 := b8e199 X0 X1 X2
               grind)
            | exact resolve b8e199 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e199
          have b8e536 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e236 (σ y) X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e236 X0 (σ y) (σ x)
               grind)
            | exact superpose b8e236 b8e24
            | (have j1 := b8e236 (σ y) X0 x
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e236 (σ x) (σ y) (σ x)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e236 (σ y) (σ x) (σ x)
               grind)
            | exact resolve b8e24 b8e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e577 : ∀ X0 : G, (M.op X0 (σ x)) ≠ (σ (M.op x x)) ∨ (M.op X0 (σ y)) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b8e536 X0
               have i₂ := b8e88 x
               grind)
            | exact superpose b8e88 b8e536
            | (have j0 := b8e536 X0
               grind)
            | exact resolve b8e536 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e536
          have b8e15185 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b8e577 (σ x)
               have i₂ := b8e88 x
               grind)
            | exact superpose b8e88 b8e577
            | (have j0 := b8e577 (σ x)
               grind)
            | (have r₁ := b8e577 (σ x)
               have r₂ := b8e88 x
               grind)
            | exact resolve b8e577 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88 b8e577
          have b8e15208 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b8e15185
          have b8e15221 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e15208
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e15208
            | exact resolve b8e15208 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15208
          have b8e15232 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e15221
               grind)
            | exact superpose b8e15221 b8e20
            | exact resolve b8e20 b8e15221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15221
          have b8e15333 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e15232
               have i₂ := b8e236 y x X0
               grind)
            | exact superpose b8e236 b8e15232
            | (have j1 := b8e236 x y X0
               grind)
            | exact resolve b8e15232 b8e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e236 b8e15232
          have b8e15338 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b8e15333 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15333
          have b8e15767 : (M.op x x) ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e15338 x
               grind)
            | exact superpose b8e15338 b8e22
            | (have r₁ := b8e22
               have r₂ := b8e15338 x
               grind)
            | exact resolve b8e22 b8e15338
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15338
          have b8e15877 : False := by grind
          exact b8e15877

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
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
      have b0e99 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
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
      have b0e102 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e99 x X1 x
           have i₂ := b0e11 X1 x x x
           grind)
        | exact superpose b0e11 b0e99
        | exact resolve b0e99 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99
      have b0e131 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e333 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e131 (σ x)
           grind)
        | exact superpose b0e131 b0e18
        | exact resolve b0e18 b0e131
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e131
      have b0e337 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e333
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e333
        | exact resolve b0e333 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e333
      have b0e348 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e337
           have i₂ := b0e102 x
           grind)
        | exact superpose b0e102 b0e337
        | exact resolve b0e337 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102 b0e337
      have b0e352 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e348
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e348
        | exact resolve b0e348 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e348
      have b0e353 : False := by grind
      exact b0e353
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
        have b1e48 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e51 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e53 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e51
             have r₂ := b1e21
             grind)
          | exact resolve b1e51 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e55 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e53
          | exact resolve b1e53 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e55
          | exact resolve b1e55 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e55
        have b1e60 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e13
          | exact resolve b1e13 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : x = y := by
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
        have b1e89 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e24
          | exact resolve b1e24 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e61
        have b1e91 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e89
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e89
          | exact resolve b1e89 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e89
        have b1e92 : False := by grind
        exact b1e92
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
        have b2e626 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e627 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e626
             have r₂ := b2e22
             grind)
          | exact resolve b2e626 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626
        have b2e628 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e627
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e627
          | exact resolve b2e627 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e627
        have b2e629 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e628
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e628
          | exact resolve b2e628 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e628
        have b2e630 : False := by grind
        exact b2e630
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
        have b3e58 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e62 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e58
        have b3e65 : y = (k x y) := by
          first
          | (have r₁ := b3e62
             have r₂ := b3e20
             grind)
          | exact resolve b3e62 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e66 : x = y := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e65
          | exact resolve b3e65 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e65
        have b3e68 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e24
          | exact resolve b3e24 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e71 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e72 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e71
          | exact resolve b3e71 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66 b3e71
        have b3e73 : False := by grind
        exact b3e73
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
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b5e30 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b5e27
          have b5e34 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
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
          have b5e35 : ∀ X0 X1 : G, (M.op x X0) = (M.op x (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 y X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b5e37 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op X0 X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
          have b5e39 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b5e40 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b5e38 x X1 X2 X3 x
               have i₂ := b5e13 X2 X1 x x
               grind)
            | exact superpose b5e13 b5e38
            | exact resolve b5e38 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e41 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e36 X0 x X2 X3 x
               have i₂ := b5e13 X0 X3 x x
               grind)
            | exact superpose b5e13 b5e36
            | exact resolve b5e36 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e42 : x = (M.op x x) := by
            first
            | (have i₁ := b5e35 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e49 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e52 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e49
          have b5e55 : y = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e66 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op (M.op X1 X3) X0) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 X3 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2 X3
               have i₂ := b5e18 X0 (M.op X3 X1)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b5e72 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e66 X0 X1 X2 x
               have i₂ := b5e41 X1 x X0
               grind)
            | exact superpose b5e41 b5e66
            | (have j0 := b5e66 X0 X1 X2 x
               grind)
            | exact resolve b5e66 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e76 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e21
            | exact resolve b5e21 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : x = (k x x) := by grind
          have b5e89 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op (M.op X1 X2) (M.op X0 y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 x X2 (M.op X0 x)
               have i₂ := b5e37 X0 x
               grind)
            | exact superpose b5e37 b5e13
            | exact resolve b5e13 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e92 : ∀ X1 : G, (M.op X1 y) = (M.op X1 x) := by
            intro X1
            first
            | (have i₁ := b5e89 x X1 x
               have i₂ := b5e13 X1 y x x
               grind)
            | exact superpose b5e13 b5e89
            | exact resolve b5e89 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e148 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X0 X2) X1
               have i₂ := b5e41 X0 X2 X1
               grind)
            | exact superpose b5e41 b5e17
            | (have j0 := b5e17 (M.op X0 X2) X1
               grind)
            | (have r₁ := b5e17 (M.op X0 x) x
               have r₂ := b5e41 X0 x x
               grind)
            | exact resolve b5e17 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e155 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e148 X0 X1 X2
               have i₂ := b5e13 X0 X2 X2 X0
               grind)
            | exact superpose b5e13 b5e148
            | (have j0 := b5e148 X0 X1 X2
               grind)
            | exact resolve b5e148 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e148
          have b5e189 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e437 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e456 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e72 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e528 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e529 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e528
               have r₂ := b5e24
               grind)
            | exact resolve b5e528 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e528
          have b5e530 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e529
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e529
            | exact resolve b5e529 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e529
          have b5e531 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e530
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e530
            | exact resolve b5e530 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e530
          have b5e536 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e531
               grind)
            | exact superpose b5e531 b5e24
            | exact resolve b5e24 b5e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e541 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b5e39 (σ x) (σ y)
               have i₂ := b5e531
               grind)
            | exact superpose b5e531 b5e39
            | exact resolve b5e39 b5e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e547 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e541
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e541
            | exact resolve b5e541 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e541
          have b5e651 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e547
               grind)
            | exact superpose b5e547 b5e14
            | exact resolve b5e14 b5e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e547
          have b5e653 : y = (k y y) := by
            first
            | (have i₁ := b5e651
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e651
            | exact resolve b5e651 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e651
          have b5e706 : ∀ X0 X1 X2 : G, (M.op (σ X0) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41 (σ X0) (σ X1) X2
               have i₂ := b5e60 X0 X1
               grind)
            | exact superpose b5e60 b5e41
            | (have j1 := b5e60 X0 X1
               grind)
            | exact resolve b5e41 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e801 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e653
               grind)
            | exact superpose b5e653 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e653
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e653
          have b5e802 : y = (M.op y y) := by grind
          clear b5e801
          have b5e805 : y = (M.op y x) := by
            first
            | (have i₁ := b5e802
               have i₂ := b5e92 y
               grind)
            | exact superpose b5e92 b5e802
            | exact resolve b5e802 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e802
          have b5e1566 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e456 x X0
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e456
            | (have j0 := b5e456 x X0
               grind)
            | (have r₁ := b5e456 x x
               have r₂ := b5e42
               grind)
            | exact resolve b5e456 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e456
          have b5e1567 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b5e1566 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1566
          have b5e1600 : x = (M.op x (σ (M.op (τ x) (τ x)))) ∨ x = (M.op x (σ (M.op (τ x) (τ x)))) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e1567 (σ (M.op (τ x) (τ x)))
               grind)
            | exact superpose b5e1567 b5e34
            | (have j1 := b5e1567 (σ (M.op (τ x) (τ x)))
               grind)
            | exact resolve b5e34 b5e1567
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1567
          have b5e1606 : x = (M.op x (σ (M.op (τ x) (τ x)))) := by grind
          clear b5e1600
          have b5e1708 : x ≠ x ∨ (M.op x x) = (σ (M.op (τ x) (τ x))) ∨ (σ (M.op (τ x) (τ x))) = (k x (σ (M.op (τ x) (τ x)))) := by
            first
            | (have i₁ := b5e17 x (σ (M.op (τ x) (τ x)))
               have i₂ := b5e1606
               grind)
            | exact superpose b5e1606 b5e17
            | (have j0 := b5e17 x (σ (M.op (τ x) (τ x)))
               grind)
            | (have r₁ := b5e17 x (σ (M.op (τ x) (τ x)))
               have r₂ := b5e1606
               grind)
            | exact resolve b5e17 b5e1606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1712 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ (M.op (τ x) (τ x)))) := by
            intro X0
            first
            | (have i₁ := b5e40 (σ (M.op (τ x) (τ x))) X0 x
               have i₂ := b5e1606
               grind)
            | exact superpose b5e1606 b5e40
            | exact resolve b5e40 b5e1606
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1606
          have b5e1718 : (M.op x x) = (σ (M.op (τ x) (τ x))) ∨ (σ (M.op (τ x) (τ x))) = (k x (σ (M.op (τ x) (τ x)))) := by grind
          clear b5e1708
          have b5e1719 : x = (σ (M.op (τ x) (τ x))) ∨ (σ (M.op (τ x) (τ x))) = (k x (σ (M.op (τ x) (τ x)))) := by
            first
            | (have i₁ := b5e1718
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e1718
            | exact resolve b5e1718 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1718
          have b5e1722 : x = (σ (M.op (τ x) (τ x))) ∨ x = (σ (M.op (τ x) (τ x))) := by
            first
            | (have i₁ := b5e1719
               have i₂ := b5e34 x
               grind)
            | exact superpose b5e34 b5e1719
            | exact resolve b5e1719 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e1719
          have b5e1723 : x = (σ (M.op (τ x) (τ x))) := by grind
          clear b5e1722
          have b5e1837 : ∀ X0 : G, (k (M.op (τ x) (τ x)) (τ X0)) = (τ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b5e189 (M.op (τ x) (τ x)) X0
               have i₂ := b5e1723
               grind)
            | exact superpose b5e1723 b5e189
            | exact resolve b5e189 b5e1723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2295 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e155 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e155
          have b5e2810 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op X1 (τ X0))) X0) ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e28 X0 (M.op X1 (τ X0))
               have i₂ := b5e2295 X1 (τ X0)
               grind)
            | exact superpose b5e2295 b5e28
            | (have j1 := b5e2295 X1 (τ X0)
               grind)
            | exact resolve b5e28 b5e2295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e2295
          have b5e2812 : ∀ X0 X1 : G, (k (σ (M.op X1 (τ X0))) X0) = X0 ∨ (τ X0) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2810 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e2810
            | (have j0 := b5e2810 X0 X1
               grind)
            | exact resolve b5e2810 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2810
          have b5e2825 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X2 X1)) ∨ (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e437 X2 (M.op x X1)
               have i₂ := b5e40 X1 X2 x
               grind)
            | exact superpose b5e40 b5e437
            | (have j0 := b5e437 X0 X1
               grind)
            | exact resolve b5e437 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e437
          have b5e14778 : ∀ X0 X1 : G, (M.op (σ (M.op (τ x) (τ x))) X1) = (M.op (σ (τ (k x X0))) X1) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ x) (τ x))) (σ (M.op (τ x) (τ x)))) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e706 (M.op (τ x) (τ x)) (τ X0) X1
               have i₂ := b5e1837 X0
               grind)
            | exact superpose b5e1837 b5e706
            | (have j0 := b5e706 (M.op (τ x) (τ x)) (τ X0) x
               grind)
            | exact resolve b5e706 b5e1837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e706 b5e1837
          have b5e15323 : ∀ X0 X1 : G, (M.op (σ (M.op (τ x) (τ x))) X1) = (M.op (k x X0) X1) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ x) (τ x))) (σ (M.op (τ x) (τ x)))) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14778 X0 X1
               have i₂ := b5e15 (k x X0)
               grind)
            | exact superpose b5e15 b5e14778
            | (have j0 := b5e14778 X0 X1
               grind)
            | exact resolve b5e14778 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14778
          have b5e15406 : ∀ X0 X1 : G, (M.op x X1) = (M.op (k x X0) X1) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ x) (τ x))) (σ (M.op (τ x) (τ x)))) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15323 X0 X1
               have i₂ := b5e1723
               grind)
            | exact superpose b5e1723 b5e15323
            | (have j0 := b5e15323 X0 X1
               grind)
            | exact resolve b5e15323 b5e1723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15323
          have b5e15446 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (σ (M.op (τ x) (τ x))) x) ∨ (M.op x X1) = (M.op (k x X0) X1) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15406 X0 X1
               have i₂ := b5e1712 (σ (M.op (τ x) (τ x)))
               grind)
            | exact superpose b5e1712 b5e15406
            | (have j0 := b5e15406 X0 X1
               grind)
            | exact resolve b5e15406 b5e1712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1712 b5e15406
          have b5e15461 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op x x) ∨ (M.op x X1) = (M.op (k x X0) X1) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15446 X0 X1
               have i₂ := b5e1723
               grind)
            | exact superpose b5e1723 b5e15446
            | (have j0 := b5e15446 X0 X1
               grind)
            | exact resolve b5e15446 b5e1723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15446
          have b5e15473 : ∀ X0 X1 : G, (σ (τ X0)) = x ∨ (M.op x X1) = (M.op (k x X0) X1) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15461 X0 X1
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e15461
            | (have j0 := b5e15461 X0 X1
               grind)
            | exact resolve b5e15461 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e15461
          have b5e15478 : ∀ X0 X1 : G, x = X0 ∨ (M.op x X1) = (M.op (k x X0) X1) ∨ (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15473 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e15473
            | (have j0 := b5e15473 X0 X1
               grind)
            | exact resolve b5e15473 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15473
          have b5e15480 : ∀ X0 X1 : G, (σ (M.op (τ x) (τ x))) = (M.op (σ (M.op (τ x) (τ x))) X0) ∨ x = X0 ∨ (M.op x X1) = (M.op (k x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e15478 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e15478
            | (have j0 := b5e15478 X0 X1
               grind)
            | exact resolve b5e15478 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15478
          have b5e15482 : ∀ X0 X1 : G, (M.op x X1) = (M.op (k x X0) X1) ∨ x = X0 ∨ x = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e15480 X0 X1
               have i₂ := b5e1723
               grind)
            | exact superpose b5e1723 b5e15480
            | (have j0 := b5e15480 X0 X1
               grind)
            | exact resolve b5e15480 b5e1723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1723 b5e15480
          have b5e167830 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2825 (σ x) (σ y) x
               have i₂ := b5e531
               grind)
            | exact superpose b5e531 b5e2825
            | exact resolve b5e2825 b5e531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e531 b5e2825
          have b5e168647 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have j0 := b5e167830 X0
               grind)
            | (have r₁ := b5e167830 X0
               have r₂ := b5e536
               grind)
            | exact resolve b5e167830 b5e536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167830
          have b5e168831 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e168647 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e168647
            | (have j0 := b5e168647 X0
               grind)
            | exact resolve b5e168647 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168647
          have b5e168923 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e168831 X0
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e168831
            | (have j0 := b5e168831 X0
               grind)
            | exact resolve b5e168831 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e168831
          have b5e168954 : ∀ X0 : G, (σ y) = (k (σ x) (M.op X0 (σ y))) := by
            intro X0
            first
            | (have j0 := b5e168923 X0
               grind)
            | (have r₁ := b5e168923 X0
               have r₂ := b5e536
               grind)
            | exact resolve b5e168923 b5e536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e536 b5e168923
          have b5e169132 : ∀ X0 : G, (τ (σ y)) = (k x (τ (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e189 x (M.op X0 (σ y))
               have i₂ := b5e168954 X0
               grind)
            | exact superpose b5e168954 b5e189
            | exact resolve b5e189 b5e168954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e189
          have b5e169272 : ∀ X0 : G, y = (k x (τ (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e169132 X0
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e169132
            | exact resolve b5e169132 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169132
          have b5e213730 : ∀ X0 : G, (M.op x y) = (M.op (k x X0) x) ∨ x = X0 ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e92 (k x X0)
               have i₂ := b5e15482 X0 y
               grind)
            | exact superpose b5e15482 b5e92
            | (have j1 := b5e15482 X0 x
               grind)
            | exact resolve b5e92 b5e15482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92 b5e15482
          have b5e213749 : ∀ X0 : G, x = (M.op (k x X0) x) ∨ x = X0 ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e213730 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e213730
            | (have j0 := b5e213730 X0
               grind)
            | exact resolve b5e213730 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213730
          have b5e213826 : ∀ X0 : G, x = (M.op y x) ∨ x = (τ (M.op X0 (σ y))) ∨ x = (M.op x (τ (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e213749 (τ (M.op X0 (σ y)))
               have i₂ := b5e169272 X0
               grind)
            | exact superpose b5e169272 b5e213749
            | (have j0 := b5e213749 (τ (M.op X0 (σ y)))
               grind)
            | exact resolve b5e213749 b5e169272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213749
          have b5e214013 : ∀ X0 : G, x = y ∨ x = (τ (M.op X0 (σ y))) ∨ x = (M.op x (τ (M.op X0 (σ y)))) := by
            intro X0
            first
            | (have i₁ := b5e213826 X0
               have i₂ := b5e805
               grind)
            | exact superpose b5e805 b5e213826
            | (have j0 := b5e213826 X0
               grind)
            | exact resolve b5e213826 b5e805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213826
          have b5e214035 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (σ y)))) ∨ x = (τ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have j0 := b5e214013 X0
               grind)
            | (have r₁ := b5e214013 X0
               have r₂ := b5e76
               grind)
            | exact resolve b5e214013 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e214013
          have b5e214326 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ x) (M.op X0 (σ y))) ∨ x = (τ (M.op X0 (σ y))) ∨ x = (τ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e2812 (M.op X0 (σ y)) x
               have i₂ := b5e214035 X0
               grind)
            | exact superpose b5e214035 b5e2812
            | (have j1 := b5e214035 X0
               grind)
            | exact resolve b5e2812 b5e214035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2812 b5e214035
          have b5e214355 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ x) (M.op X0 (σ y))) ∨ x = (τ (M.op X0 (σ y))) := by
            intro X0
            first
            | (have j0 := b5e214326 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e214326
          have b5e214364 : ∀ X0 : G, x = (τ (M.op X0 (σ y))) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e214355 X0
               have i₂ := b5e168954 X0
               grind)
            | exact superpose b5e168954 b5e214355
            | (have j0 := b5e214355 X0
               grind)
            | exact resolve b5e214355 b5e168954
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168954 b5e214355
          have b5e214741 : ∀ X0 : G, y = (k x x) ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e169272 X0
               have i₂ := b5e214364 X0
               grind)
            | exact superpose b5e214364 b5e169272
            | (have j1 := b5e214364 X0
               grind)
            | exact resolve b5e169272 b5e214364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169272 b5e214364
          have b5e214860 : ∀ X0 : G, x = y ∨ (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e214741 X0
               have i₂ := b5e77
               grind)
            | exact superpose b5e77 b5e214741
            | (have j0 := b5e214741 X0
               grind)
            | exact resolve b5e214741 b5e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77 b5e214741
          have b5e214885 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e214860 X0
               grind)
            | (have r₁ := b5e214860 X0
               have r₂ := b5e76
               grind)
            | exact resolve b5e214860 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76 b5e214860
          have b5e215073 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X0 (σ y) X1
               have i₂ := b5e214885 X0
               grind)
            | exact superpose b5e214885 b5e41
            | exact resolve b5e41 b5e214885
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e214885
          have b5e215800 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e215073 X0 X1
               have i₂ := b5e215073 X2 X1
               grind)
            | (have i₁ := b5e215073 X0 X1
               have i₂ := b5e215073 (σ y) X1
               grind)
            | exact superpose b5e215073 b5e215073
            | exact resolve b5e215073 b5e215073
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e215073
          have b5e219902 : ∀ X0 : G, y ≠ (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e215800 x x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e215800 X0 x x
               grind)
            | exact superpose b5e215800 b5e21
            | exact resolve b5e21 b5e215800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e219914 : ∀ X0 : G, y = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b5e805
               have i₂ := b5e215800 y x X0
               grind)
            | (have i₁ := b5e805
               have i₂ := b5e215800 X0 x y
               grind)
            | exact superpose b5e215800 b5e805
            | exact resolve b5e805 b5e215800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e805 b5e215800
          have b5e219919 : False := by grind
          exact b5e219919
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
        have b6e92 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e104 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e92
        have b6e112 : y = (M.op x x) := by
          first
          | (have r₁ := b6e104
             have r₂ := b6e21
             grind)
          | exact resolve b6e104 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e121 : False := by grind
        exact b6e121
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
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
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b7e29 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y) X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b7e31 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (M.op X0 X1) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 (σ y) X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op X3 X1)) = (M.op (M.op X2 X4) (M.op X0 X1)) := by
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
          have b7e33 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            grind
          have b7e34 : ∀ X1 X2 X3 : G, (M.op X2 (M.op X3 X1)) = (M.op X2 X1) := by
            intro X1 X2 X3
            first
            | (have i₁ := b7e32 x X1 X2 X3 x
               have i₂ := b7e13 X2 X1 x x
               grind)
            | exact superpose b7e13 b7e32
            | exact resolve b7e32 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e35 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e30 X0 x X2 X3 x
               have i₂ := b7e13 X0 X3 x x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e36 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) X0 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e48
          have b7e53 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e54 : (σ y) = (σ (k x y)) := by
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
          have b7e57 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e14
            | exact resolve b7e14 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e58 : y = (k x y) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e57
            | exact resolve b7e57 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e64 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X2 ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e18 X1 X2
               have i₂ := b7e18 X1 X0
               grind)
            | (have i₁ := b7e18 X0 X1
               have i₂ := b7e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e18 b7e18
            | (have j0 := b7e18 X1 X2
               have j1 := b7e18 X1 X2
               grind)
            | exact resolve b7e18 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b7e67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e69 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 X0) ∨ (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X2 X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 X2 X1 X2
               have i₂ := b7e18 X2 X0
               grind)
            | (have i₁ := b7e34 X1 X2 x
               have i₂ := b7e18 X0 (M.op x X1)
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 X2 X0
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
          have b7e77 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e71 X0 X1 X2 x
               have i₂ := b7e34 X2 X0 x
               grind)
            | exact superpose b7e34 b7e71
            | (have j0 := b7e71 X0 X1 X2 x
               grind)
            | exact resolve b7e71 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
          have b7e91 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e21
               grind)
            | exact resolve b7e90 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e93 : y = (M.op x y) := by
            first
            | (have r₁ := b7e91
               have r₂ := b7e22
               grind)
            | exact resolve b7e91 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e105 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op (M.op X0 X2) (M.op X0 X2)) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 (M.op X0 X2) X1
               have i₂ := b7e35 X0 X2 X1
               grind)
            | exact superpose b7e35 b7e17
            | (have j0 := b7e17 (M.op X0 X2) X1
               grind)
            | (have r₁ := b7e17 (M.op X0 x) x
               have r₂ := b7e35 X0 x x
               grind)
            | exact resolve b7e17 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X2) ∨ (M.op X0 X2) = X1 ∨ (k (M.op X0 X2) X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e105 X0 X1 X2
               have i₂ := b7e13 X0 X2 X2 X0
               grind)
            | exact superpose b7e13 b7e105
            | (have j0 := b7e105 X0 X1 X2
               grind)
            | exact resolve b7e105 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e123 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e26
            | exact resolve b7e26 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e124 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e22
            | exact resolve b7e22 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e125 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e35 x y X0
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e35
            | exact resolve b7e35 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e131 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          have b7e135 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b7e136 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e131 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e131
            | exact resolve b7e131 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e131
          have b7e143 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b7e150 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e29 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e197 : y = (k y (M.op x y)) := by grind
          have b7e211 : y = (k y y) := by
            first
            | (have i₁ := b7e197
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e197
            | exact resolve b7e197 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e197
          have b7e219 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e33 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e33
            | exact resolve b7e33 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e227 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e219
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e219
            | exact resolve b7e219 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e219
          have b7e237 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 ∨ (M.op X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e28 X1 X0
               have i₂ := b7e67 (τ X1) X0
               grind)
            | exact superpose b7e67 b7e28
            | (have j1 := b7e67 (τ X1) X0
               grind)
            | exact resolve b7e28 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e253 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e227
               grind)
            | exact superpose b7e227 b7e14
            | exact resolve b7e14 b7e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e227
          have b7e255 : x = (k x x) := by
            first
            | (have i₁ := b7e253
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e253
            | exact resolve b7e253 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e253
          have b7e288 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e299 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X2 X3)) = (k X0 (M.op X2 X3)) ∨ (M.op X0 (M.op X2 X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e35 X2 X3 X1
               have i₂ := b7e77 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b7e35 X0 X2 X2
               have i₂ := b7e77 X0 (M.op X0 X2) X2
               grind)
            | exact superpose b7e77 b7e35
            | (have j1 := b7e77 (M.op X2 X3) X0 X2
               grind)
            | exact resolve b7e35 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e305 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X2 ∨ (M.op X1 X2) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e18 X1 X2
               have i₂ := b7e77 X0 X1 X1
               grind)
            | (have i₁ := b7e18 X2 X1
               have i₂ := b7e77 X2 X1 X2
               grind)
            | exact superpose b7e77 b7e18
            | (have j0 := b7e18 X1 X2
               have j1 := b7e77 X2 X1 X2
               grind)
            | exact resolve b7e18 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e339 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 (M.op X2 X3)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e299 X0 X1 X2 X3
               have i₂ := b7e34 X3 X0 X2
               grind)
            | exact superpose b7e34 b7e299
            | (have j0 := b7e299 X0 X1 X2 X3
               grind)
            | exact resolve b7e299 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e299
          have b7e364 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X0 X3) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e339 X0 X1 X2 X3
               have i₂ := b7e34 X3 X0 X2
               grind)
            | exact superpose b7e34 b7e339
            | (have j0 := b7e339 X0 X1 X2 X3
               grind)
            | exact resolve b7e339 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e339
          have b7e386 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e255
               grind)
            | exact superpose b7e255 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e255
          have b7e387 : x = (M.op x x) := by grind
          clear b7e386
          have b7e589 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ X1)) ∨ (M.op (σ X0) X2) = (k (σ X0) X2) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e77 X2 (σ X0) (σ X1)
               have i₂ := b7e65 X0 X1
               grind)
            | exact superpose b7e65 b7e77
            | (have j0 := b7e77 X2 (σ X0) X2
               have j1 := b7e65 X0 X1
               grind)
            | exact resolve b7e77 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e608 : ∀ X0 X1 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (M.op X1 (σ X2)) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e34 (σ X2) X1 (σ X2)
               have i₂ := b7e65 X2 X0
               grind)
            | exact superpose b7e65 b7e34
            | (have j1 := b7e65 X2 X0
               grind)
            | exact resolve b7e34 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e615 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e65 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e616 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b7e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e617 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e615 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e615
          have b7e677 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e135 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e135
            | exact resolve b7e135 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e802 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b7e819 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e802 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e802
            | exact resolve b7e802 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e802
          have b7e919 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
            intro X0
            first
            | (have i₁ := b7e143 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
               have i₂ := b7e819 (σ X0)
               grind)
            | exact superpose b7e819 b7e143
            | exact resolve b7e143 b7e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e936 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e919 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e919
            | exact resolve b7e919 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e919
          have b7e1226 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e617 (M.op X0 X1)
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e617
            | (have j0 := b7e617 (M.op X0 X1)
               grind)
            | exact resolve b7e617 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1230 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e617 y
               have i₂ := b7e211
               grind)
            | exact superpose b7e211 b7e617
            | (have j0 := b7e617 y
               grind)
            | exact resolve b7e617 b7e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e211
          have b7e1233 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e617 (τ X0)
               have i₂ := b7e28 X0 (τ X0)
               grind)
            | exact superpose b7e28 b7e617
            | (have j0 := b7e617 (τ X0)
               grind)
            | exact resolve b7e617 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1236 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b7e1230
          have b7e1238 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b7e1226 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1226
          have b7e1240 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e1233 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1233
            | (have j0 := b7e1233 X0
               grind)
            | exact resolve b7e1233 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1233
          have b7e1242 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e1236
               have i₂ := b7e36 (σ y)
               grind)
            | exact superpose b7e36 b7e1236
            | exact resolve b7e1236 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1236
          have b7e1244 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1240 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e1240
            | (have j0 := b7e1240 X0
               grind)
            | exact resolve b7e1240 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1240
          have b7e1254 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e1242
               grind)
            | exact superpose b7e1242 b7e17
            | (have j0 := b7e17 (σ y) (σ x)
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e1242
               grind)
            | exact resolve b7e17 b7e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1264 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
          clear b7e1254
          have b7e1267 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e1264
               have i₂ := b7e36 (σ y)
               grind)
            | exact superpose b7e36 b7e1264
            | exact resolve b7e1264 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1264
          have b7e1273 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e1267
               have i₂ := b7e1242
               grind)
            | exact superpose b7e1242 b7e1267
            | exact resolve b7e1267 b7e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1267
          have b7e1275 : (σ x) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b7e1273
               have r₂ := b7e123
               grind)
            | exact resolve b7e1273 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1273
          have b7e1276 : (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1275
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e1275
            | exact resolve b7e1275 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1275
          have b7e1372 : (τ (σ x)) = (k y x) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1276
               grind)
            | exact superpose b7e1276 b7e14
            | exact resolve b7e14 b7e1276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1374 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (k y x))) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 (k y x)
               have i₂ := b7e1276
               grind)
            | exact superpose b7e1276 b7e19
            | exact resolve b7e19 b7e1276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1276
          have b7e1402 : ∀ X0 : G, (σ (k X0 x)) = (σ (k X0 (k y x))) := by
            intro X0
            first
            | (have i₁ := b7e1374 X0
               have i₂ := b7e19 X0 x
               grind)
            | exact superpose b7e19 b7e1374
            | exact resolve b7e1374 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1374
          have b7e1404 : x = (k y x) := by
            first
            | (have i₁ := b7e1372
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1372
            | exact resolve b7e1372 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1372
          have b7e1536 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e1244 (τ X0)
               have i₂ := b7e677 X0 X0
               grind)
            | exact superpose b7e677 b7e1244
            | (have j0 := b7e1244 (τ X0)
               grind)
            | exact resolve b7e1244 b7e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1812 : ∀ X0 X1 : G, (k X0 (M.op X0 X1)) = X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e1844 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e69 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e2033 : ∀ X0 X1 : G, (k (M.op X0 X1) X1) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e112 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e2154 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X2) X1) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e288 (M.op X0 X2) x
               have i₂ := b7e35 X0 X2 x
               grind)
            | exact superpose b7e35 b7e288
            | (have j0 := b7e288 X0 X1
               grind)
            | exact resolve b7e288 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e288
          have b7e2745 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X2 X3) = (M.op (M.op X2 X3) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e35 X2 X3 X1
               have i₂ := b7e364 (M.op X2 X3) X1 X0 X4
               grind)
            | (have i₁ := b7e35 X0 X2 X1
               have i₂ := b7e364 X0 X1 (M.op X0 X2) X3
               grind)
            | exact superpose b7e364 b7e35
            | (have j1 := b7e364 (M.op X2 X3) X1 X0 X4
               grind)
            | exact resolve b7e35 b7e364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e364
          have b7e2806 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X3) = (M.op (M.op X2 X3) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e2745 X0 X1 X2 X3 X4
               have i₂ := b7e35 X2 X3 X4
               grind)
            | exact superpose b7e35 b7e2745
            | (have j0 := b7e2745 X0 X1 X2 X3 X4
               grind)
            | exact resolve b7e2745 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2745
          have b7e2838 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X4) = (k (M.op X2 X3) (M.op X0 X4)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X3) = (M.op X2 X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e2806 X0 X1 X2 X3 X4
               have i₂ := b7e35 X2 X3 X4
               grind)
            | exact superpose b7e35 b7e2806
            | (have j0 := b7e2806 X0 X1 X2 X3 X4
               grind)
            | exact resolve b7e2806 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2806
          have b7e3144 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e237 X0 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e237
            | exact resolve b7e237 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237
          have b7e3191 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e3144 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e3144
            | (have j0 := b7e3144 X0 X1
               grind)
            | exact resolve b7e3144 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3144
          have b7e4088 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            grind
          clear b7e616
          have b7e4149 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b7e4088 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4088
          have b7e7655 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1536 (M.op X0 X1)
               have i₂ := b7e33 X0 X1
               grind)
            | exact superpose b7e33 b7e1536
            | (have j0 := b7e1536 (M.op X0 X1)
               grind)
            | exact resolve b7e1536 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e7673 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b7e7655 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7655
          have b7e9880 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e150
               have i₂ := b7e608 X0 (σ x) x
               grind)
            | (have i₁ := b7e150
               have i₂ := b7e608 x (σ x) x
               grind)
            | exact superpose b7e608 b7e150
            | (have j1 := b7e608 X0 x x
               grind)
            | exact resolve b7e150 b7e608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e608
          have b7e9971 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e9880 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9880
          have b7e11183 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e305 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e305
          have b7e11257 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e11183 X0 X1
               have j1 := b7e64 X1 X0 X1
               grind)
            | (have r₁ := b7e11183 (M.op X1 x) (k X1 x)
               have r₂ := b7e64 X0 X1 x
               grind)
            | (have r₁ := b7e11183 (k X1 x) (M.op X1 x)
               have r₂ := b7e64 X0 X1 x
               grind)
            | (have r₁ := b7e11183 (M.op X1 X0) (k X1 X0)
               have r₂ := b7e64 X0 X1 x
               grind)
            | exact resolve b7e11183 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e11183
          have b7e11337 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e11257 X0 X1
               have j1 := b7e1844 X0 X1
               grind)
            | (have r₁ := b7e11257 X0 X0
               have r₂ := b7e1844 X0 X1
               grind)
            | (have r₁ := b7e11257 X0 X1
               have r₂ := b7e1844 X0 X1
               grind)
            | exact resolve b7e11257 b7e1844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11257
          have b7e29777 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e1844 (σ y) X0
               have i₂ := b7e36 (σ y)
               grind)
            | exact superpose b7e36 b7e1844
            | (have j0 := b7e1844 (σ y) X0
               grind)
            | exact resolve b7e1844 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29782 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e1844 (M.op X0 X1) X2
               have i₂ := b7e13 X0 X1 X1 X0
               grind)
            | exact superpose b7e13 b7e1844
            | (have j0 := b7e1844 (M.op X0 X1) X2
               grind)
            | (have r₁ := b7e1844 (M.op x X1) X1
               have r₂ := b7e13 x X1 X1 x
               grind)
            | exact resolve b7e1844 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29819 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k y X0) = (M.op y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e1844 y X0
               have i₂ := b7e125 y
               grind)
            | exact superpose b7e125 b7e1844
            | (have j0 := b7e1844 y X0
               grind)
            | exact resolve b7e1844 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29838 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e29782 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29782
          have b7e29840 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e29819 X0
               grind)
            | (have r₁ := b7e29819 X0
               have r₂ := b7e93
               grind)
            | exact resolve b7e29819 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29819
          have b7e29845 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e29838 X0 X1 X2
               have i₂ := b7e35 X0 X1 X2
               grind)
            | exact superpose b7e35 b7e29838
            | (have j0 := b7e29838 X0 X1 X2
               grind)
            | exact resolve b7e29838 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29838
          have b7e29847 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e29777 X0
               grind)
            | (have r₁ := b7e29777 X0
               have r₂ := b7e1242
               grind)
            | exact resolve b7e29777 b7e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29777
          have b7e29852 : ∀ X0 : G, (k y X0) = (M.op x X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e29840 X0
               have i₂ := b7e125 X0
               grind)
            | exact superpose b7e125 b7e29840
            | (have j0 := b7e29840 X0
               grind)
            | exact resolve b7e29840 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29840
          have b7e29856 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (k (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e29845 X0 X1 X2
               have i₂ := b7e35 X0 X1 X2
               grind)
            | exact superpose b7e35 b7e29845
            | (have j0 := b7e29845 X0 X1 X2
               grind)
            | exact resolve b7e29845 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29845
          have b7e29859 : ∀ X0 : G, (k y X0) = (M.op x X0) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e29852 X0
               have i₂ := b7e125 X0
               grind)
            | exact superpose b7e125 b7e29852
            | (have j0 := b7e29852 X0
               grind)
            | exact resolve b7e29852 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29852
          have b7e32850 : ∀ X0 : G, (k (τ y) X0) = (τ (M.op x (σ X0))) ∨ y = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e135 y X0
               have i₂ := b7e29859 (σ X0)
               grind)
            | exact superpose b7e29859 b7e135
            | (have j1 := b7e29859 (σ X0)
               grind)
            | exact resolve b7e135 b7e29859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32861 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op x (τ X0))) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e28 X0 y
               have i₂ := b7e29859 (τ X0)
               grind)
            | exact superpose b7e29859 b7e28
            | (have j1 := b7e29859 (τ X0)
               grind)
            | exact resolve b7e28 b7e29859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e29859
          have b7e34843 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e143 y X0
               have i₂ := b7e29847 X0
               grind)
            | exact superpose b7e29847 b7e143
            | (have j1 := b7e29847 X0
               grind)
            | exact resolve b7e143 b7e29847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29847
          have b7e37517 : ∀ X0 X1 : G, (σ (M.op X0 (k y x))) = (σ (k (M.op X0 X1) x)) ∨ (M.op X0 X1) = (M.op X0 (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1402 (M.op X0 X1)
               have i₂ := b7e29856 X0 X1 (k y x)
               grind)
            | exact superpose b7e29856 b7e1402
            | (have j1 := b7e29856 X0 X1 (k y x)
               grind)
            | exact resolve b7e1402 b7e29856
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1402 b7e29856
          have b7e37547 : ∀ X0 X1 : G, (σ (M.op X0 x)) = (σ (k (M.op X0 X1) x)) ∨ (M.op X0 X1) = (M.op X0 (k y x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e37517 X0 X1
               have i₂ := b7e1404
               grind)
            | exact superpose b7e1404 b7e37517
            | (have j0 := b7e37517 X0 X1
               grind)
            | exact resolve b7e37517 b7e1404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37517
          have b7e37582 : ∀ X0 X1 : G, (σ (M.op X0 x)) = (σ (k (M.op X0 X1) x)) ∨ (M.op X0 X1) = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e37547 X0 X1
               have i₂ := b7e1404
               grind)
            | exact superpose b7e1404 b7e37547
            | (have j0 := b7e37547 X0 X1
               grind)
            | exact resolve b7e37547 b7e1404
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1404 b7e37547
          have b7e41211 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e617 X1
               have i₂ := b7e589 X1 X1 X0
               grind)
            | exact superpose b7e589 b7e617
            | (have j0 := b7e617 X1
               have j1 := b7e589 X1 X1 X0
               grind)
            | exact resolve b7e617 b7e589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e589 b7e617
          have b7e41933 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b7e41211 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41211
          have b7e42280 : ∀ X0 X1 : G, (σ X1) ≠ (M.op X0 (σ X1)) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
            intro X0 X1
            first
            | (have j0 := b7e41933 X0 X1
               have j1 := b7e1844 (σ X1) X0
               grind)
            | (have r₁ := b7e41933 (σ X1) X1
               have r₂ := b7e1844 (σ X1) (σ X1)
               grind)
            | (have r₁ := b7e41933 X0 X1
               have r₂ := b7e1844 (σ X1) X1
               grind)
            | (have r₁ := b7e41933 (σ X1) X1
               have r₂ := b7e1844 (σ X1) X1
               grind)
            | exact resolve b7e41933 b7e1844
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1844 b7e41933
          have b7e45631 : ∀ X0 : G, (τ (M.op x X0)) = (k (τ y) (τ X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e32850 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e32850
            | exact resolve b7e32850 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32850
          have b7e45730 : ∀ X0 : G, (τ (M.op x X0)) = (τ (k y X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e45631 X0
               have i₂ := b7e677 X0 y
               grind)
            | exact superpose b7e677 b7e45631
            | (have j0 := b7e45631 X0
               grind)
            | exact resolve b7e45631 b7e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45631
          have b7e47251 : ∀ X0 : G, (k y X0) = (k (k y X0) (σ (M.op (τ (M.op x X0)) (τ (M.op x X0))))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e136 (k y X0)
               have i₂ := b7e45730 X0
               grind)
            | exact superpose b7e45730 b7e136
            | (have j1 := b7e45730 X0
               grind)
            | exact resolve b7e136 b7e45730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e47264 : ∀ X0 X1 : G, (k (τ X1) (τ (M.op x X0))) = (τ (k X1 (k y X0))) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e677 (k y X0) X1
               have i₂ := b7e45730 X0
               grind)
            | exact superpose b7e45730 b7e677
            | (have j1 := b7e45730 X0
               grind)
            | exact resolve b7e677 b7e45730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45730
          have b7e47279 : ∀ X0 X1 : G, (τ (k X1 (M.op x X0))) = (τ (k X1 (k y X0))) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e47264 X0 X1
               have i₂ := b7e677 (M.op x X0) X1
               grind)
            | exact superpose b7e677 b7e47264
            | (have j0 := b7e47264 X0 X1
               grind)
            | exact resolve b7e47264 b7e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47264
          have b7e47280 : ∀ X0 : G, (k y X0) = (k (k y X0) (σ (τ (M.op x X0)))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e47251 X0
               have i₂ := b7e7673 x X0
               grind)
            | exact superpose b7e7673 b7e47251
            | (have j0 := b7e47251 X0
               grind)
            | exact resolve b7e47251 b7e7673
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e7673 b7e47251
          have b7e47304 : ∀ X0 : G, (k y X0) = (k (k y X0) (M.op x X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e47280 X0
               have i₂ := b7e15 (M.op x X0)
               grind)
            | exact superpose b7e15 b7e47280
            | (have j0 := b7e47280 X0
               grind)
            | exact resolve b7e47280 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47280
          have b7e47815 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op x X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e32861 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e32861
            | exact resolve b7e32861 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32861
          have b7e48007 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op x X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e47815 X0
               have i₂ := b7e19 y X0
               grind)
            | exact superpose b7e19 b7e47815
            | (have j0 := b7e47815 X0
               grind)
            | exact resolve b7e47815 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47815
          have b7e56856 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (k x X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e31 (σ x) (σ X0)
               have i₂ := b7e9971 X0
               grind)
            | exact superpose b7e9971 b7e31
            | (have j1 := b7e9971 X0
               grind)
            | exact resolve b7e31 b7e9971
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e9971
          have b7e56913 : ∀ X0 : G, (σ x) = (M.op (σ (k x X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e56856 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e56856
            | (have j0 := b7e56856 X0
               grind)
            | exact resolve b7e56856 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56856
          have b7e62631 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e819 X0
               have i₂ := b7e11337 X0 (τ (M.op (σ X0) (σ X0)))
               grind)
            | exact superpose b7e11337 b7e819
            | (have j1 := b7e11337 X0 X0
               grind)
            | exact resolve b7e819 b7e11337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e819 b7e11337
          have b7e62813 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e62631 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62631
          have b7e75166 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e33 X0 (τ (M.op (σ X0) (σ X0)))
               have i₂ := b7e62813 X0
               grind)
            | exact superpose b7e62813 b7e33
            | (have j1 := b7e62813 X0
               grind)
            | exact resolve b7e33 b7e62813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e75210 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e1238 X0 (τ (M.op (σ X0) (σ X0)))
               have i₂ := b7e62813 X0
               grind)
            | exact superpose b7e62813 b7e1238
            | (have j1 := b7e62813 X0
               grind)
            | exact resolve b7e1238 b7e62813
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62813
          have b7e76327 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e75166 (τ X0)
               have i₂ := b7e677 X0 X0
               grind)
            | exact superpose b7e677 b7e75166
            | exact resolve b7e75166 b7e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76443 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e75166 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75166
          have b7e78116 : ∀ X0 : G, (k X0 (τ (τ (σ (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e936 X0
               have i₂ := b7e75210 (σ X0)
               grind)
            | exact superpose b7e75210 b7e936
            | (have j1 := b7e75210 (σ X0)
               grind)
            | exact resolve b7e936 b7e75210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e936
          have b7e78219 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e78116 X0
               have i₂ := b7e14 (σ X0)
               grind)
            | exact superpose b7e14 b7e78116
            | (have j0 := b7e78116 X0
               grind)
            | exact resolve b7e78116 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78116
          have b7e78245 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e78219 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e78219
            | (have j0 := b7e78219 X0
               grind)
            | exact resolve b7e78219 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78219
          have b7e78249 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e78245 X0
               have i₂ := b7e19 X0 X0
               grind)
            | exact superpose b7e19 b7e78245
            | (have j0 := b7e78245 X0
               grind)
            | exact resolve b7e78245 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78245
          have b7e81990 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e2033 (σ X0) (σ (M.op X0 X0))
               have i₂ := b7e4149 X0
               grind)
            | exact superpose b7e4149 b7e2033
            | (have j1 := b7e4149 X0
               grind)
            | exact resolve b7e2033 b7e4149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2033 b7e4149
          have b7e82036 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e81990 X0
               have i₂ := b7e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e19 b7e81990
            | (have j0 := b7e81990 X0
               grind)
            | exact resolve b7e81990 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81990
          have b7e82166 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e82036
          have b7e82167 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b7e82166 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82166
          have b7e84366 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e34 (σ X0) X1 (σ X0)
               have i₂ := b7e78249 X0
               grind)
            | exact superpose b7e78249 b7e34
            | (have j1 := b7e78249 X0
               grind)
            | exact resolve b7e34 b7e78249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e84367 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (k X0 X0)) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e35 (σ X0) (σ X0) X1
               have i₂ := b7e78249 X0
               grind)
            | exact superpose b7e78249 b7e35
            | (have j1 := b7e78249 X0
               grind)
            | exact resolve b7e35 b7e78249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78249
          have b7e101475 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e84366 X0 X1
               have i₂ := b7e3191 X0 X0
               grind)
            | exact superpose b7e3191 b7e84366
            | (have j0 := b7e84366 X0 X1
               have j1 := b7e3191 X0 X0
               grind)
            | exact resolve b7e84366 b7e3191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84366
          have b7e101789 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e101475 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101475
          have b7e101891 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op X1 (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e101789 X0 X1
               have j1 := b7e76443 X0
               grind)
            | (have r₁ := b7e101789 X0 X1
               have r₂ := b7e76443 X0
               grind)
            | exact resolve b7e101789 b7e76443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101789
          have b7e103036 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e84367 X0 X1
               have i₂ := b7e3191 X0 X0
               grind)
            | exact superpose b7e3191 b7e84367
            | (have j0 := b7e84367 X0 X1
               have j1 := b7e3191 X0 X0
               grind)
            | exact resolve b7e84367 b7e3191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3191 b7e84367
          have b7e103351 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e103036 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103036
          have b7e103469 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e103351 X0 X1
               have j1 := b7e76443 X0
               grind)
            | (have r₁ := b7e103351 X0 X1
               have r₂ := b7e76443 X0
               grind)
            | exact resolve b7e103351 b7e76443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76443 b7e103351
          have b7e126895 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1238 X0 X0
               have i₂ := b7e101891 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b7e101891 b7e1238
            | (have j1 := b7e101891 X0 x
               grind)
            | exact resolve b7e1238 b7e101891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101891
          have b7e133715 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e2154 (σ y) (σ x) x
               have i₂ := b7e1242
               grind)
            | exact superpose b7e1242 b7e2154
            | exact resolve b7e2154 b7e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2154
          have b7e134169 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (σ y) = (k (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e133715 X0
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e133715
            | (have j0 := b7e133715 X0
               grind)
            | exact resolve b7e133715 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133715
          have b7e134246 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e134169 X0
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e134169
            | (have j0 := b7e134169 X0
               grind)
            | exact resolve b7e134169 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54 b7e134169
          have b7e134265 : ∀ X0 : G, (σ y) = (k (M.op (σ y) X0) (σ x)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e134246 X0
               grind)
            | (have r₁ := b7e134246 X0
               have r₂ := b7e123
               grind)
            | exact resolve b7e134246 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134246
          have b7e140849 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (k y X0) (k y X0))) ∨ (σ (M.op x X0)) = (σ (M.op (k y X0) (k y X0))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e82167 (k y X0)
               have i₂ := b7e48007 X0
               grind)
            | exact superpose b7e48007 b7e82167
            | (have j1 := b7e48007 X0
               grind)
            | exact resolve b7e82167 b7e48007
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48007
          have b7e140986 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e75210 X0
               have i₂ := b7e82167 X0
               grind)
            | exact superpose b7e82167 b7e75210
            | (have j0 := b7e75210 X0
               have j1 := b7e82167 X0
               grind)
            | exact resolve b7e75210 b7e82167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75210 b7e82167
          have b7e141198 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e140986 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e140986
          have b7e141321 : ∀ X0 : G, (σ (M.op x X0)) = (σ (M.op (k y X0) (k y X0))) ∨ (σ (M.op x X0)) = (σ (M.op (k y X0) (k y X0))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e140849 X0
               have i₂ := b7e1238 x X0
               grind)
            | exact superpose b7e1238 b7e140849
            | (have j0 := b7e140849 X0
               grind)
            | exact resolve b7e140849 b7e1238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1238 b7e140849
          have b7e141322 : ∀ X0 : G, (σ (M.op x X0)) = (σ (M.op (k y X0) (k y X0))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b7e141321 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141321
          have b7e142379 : ∀ X0 X1 : G, (τ (k X1 (σ X0))) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e135 X1 (M.op X0 X0)
               have i₂ := b7e141198 X0
               grind)
            | exact superpose b7e141198 b7e135
            | (have j1 := b7e141198 X0
               grind)
            | exact resolve b7e135 b7e141198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e142384 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e143 (M.op X0 X0) X1
               have i₂ := b7e141198 X0
               grind)
            | exact superpose b7e141198 b7e143
            | (have j1 := b7e141198 X0
               grind)
            | exact resolve b7e143 b7e141198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141198
          have b7e142559 : ∀ X0 X1 : G, (k X0 (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e142384 X0 X1
               have i₂ := b7e143 X0 X1
               grind)
            | exact superpose b7e143 b7e142384
            | (have j0 := b7e142384 X0 X1
               grind)
            | exact resolve b7e142384 b7e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e143 b7e142384
          have b7e142564 : ∀ X0 X1 : G, (k (τ X1) X0) = (k (τ X1) (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e142379 X0 X1
               have i₂ := b7e135 X1 X0
               grind)
            | exact superpose b7e135 b7e142379
            | (have j0 := b7e142379 X0 X1
               grind)
            | exact resolve b7e142379 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142379
          have b7e152734 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e42280 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e42280
            | exact resolve b7e42280 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42280
          have b7e202611 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op (M.op X3 X1) (M.op X0 X2)) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e152734 (M.op X3 X1) (M.op X0 X2)
               have i₂ := b7e13 X0 X1 X2 X3
               grind)
            | exact superpose b7e13 b7e152734
            | (have j0 := b7e152734 (M.op X3 X1) (M.op X0 X2)
               grind)
            | (have r₁ := b7e152734 (M.op X0 X1) (M.op X0 X2)
               have r₂ := b7e13 X0 X1 X2 X0
               grind)
            | exact resolve b7e152734 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e152734
          have b7e202725 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X3 X1) ∨ (M.op X3 X1) = (M.op (M.op X3 X1) (M.op X0 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e202611 X0 X1 X2 X3
               have i₂ := b7e13 X3 X2 X1 X0
               grind)
            | exact superpose b7e13 b7e202611
            | (have j0 := b7e202611 X0 X1 X2 X3
               grind)
            | exact resolve b7e202611 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e202611
          have b7e202731 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op X3 X2) ∨ (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X0 X1) ≠ (M.op X3 X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e202725 X0 X1 X2 X3
               have i₂ := b7e13 X3 X2 X1 X0
               grind)
            | exact superpose b7e13 b7e202725
            | (have j0 := b7e202725 X0 X1 X2 X3
               grind)
            | exact resolve b7e202725 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e202725
          have b7e202734 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (k (M.op X3 X1) (M.op X0 X2)) ∨ (M.op X3 X1) = (M.op X3 X2) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b7e202731 X0 X1 X2 X3
               have j1 := b7e2838 X0 X1 X3 X1 X2
               grind)
            | (have r₁ := b7e202731 X0 X1 X2 X2
               have r₂ := b7e2838 X0 X1 X2 X3 x
               grind)
            | (have r₁ := b7e202731 X2 X1 X2 X0
               have r₂ := b7e2838 X0 X1 X2 X3 x
               grind)
            | (have r₁ := b7e202731 X2 x X2 X2
               have r₂ := b7e2838 X0 X1 X2 x x
               grind)
            | exact resolve b7e202731 b7e2838
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2838 b7e202731
          have b7e231197 : ∀ X0 : G, (τ (σ y)) = (k (τ (M.op (σ y) X0)) x) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e135 (M.op (σ y) X0) x
               have i₂ := b7e134265 X0
               grind)
            | exact superpose b7e134265 b7e135
            | (have j1 := b7e134265 X0
               grind)
            | exact resolve b7e135 b7e134265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135 b7e134265
          have b7e231207 : ∀ X0 : G, y = (k (τ (M.op (σ y) X0)) x) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e231197 X0
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e231197
            | (have j0 := b7e231197 X0
               grind)
            | exact resolve b7e231197 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231197
          have b7e231330 : ∀ X0 : G, y = (k (k y (τ X0)) x) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e231207 X0
               have i₂ := b7e34843 X0
               grind)
            | exact superpose b7e34843 b7e231207
            | (have j0 := b7e231207 X0
               have j1 := b7e34843 X0
               grind)
            | exact resolve b7e231207 b7e34843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34843 b7e231207
          have b7e231350 : ∀ X0 : G, y = (k (k y (τ X0)) x) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b7e231330 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231330
          have b7e236322 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e103469 X0 (σ X0)
               have i₂ := b7e126895 X0
               grind)
            | exact superpose b7e126895 b7e103469
            | (have j0 := b7e103469 X0 x
               have j1 := b7e126895 X0
               grind)
            | exact resolve b7e103469 b7e126895
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103469 b7e126895
          have b7e236347 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b7e236322 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e236322
          have b7e236415 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e236347 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e236347
            | (have j0 := b7e236347 (τ X0)
               grind)
            | exact resolve b7e236347 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e236347
          have b7e236637 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e236415 X0
               have i₂ := b7e677 X0 X0
               grind)
            | exact superpose b7e677 b7e236415
            | (have j0 := b7e236415 X0
               grind)
            | exact resolve b7e236415 b7e677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e677 b7e236415
          have b7e240122 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e14 (M.op (τ X0) (τ X0))
               have i₂ := b7e236637 X0
               grind)
            | exact superpose b7e236637 b7e14
            | (have j1 := b7e236637 X0
               grind)
            | exact resolve b7e14 b7e236637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e236637
          have b7e241824 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e76327 X0
               have i₂ := b7e240122 X0
               grind)
            | exact superpose b7e240122 b7e76327
            | (have j0 := b7e76327 X0
               have j1 := b7e240122 X0
               grind)
            | exact resolve b7e76327 b7e240122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76327 b7e240122
          have b7e241919 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have j0 := b7e241824 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e241824
          have b7e242491 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e1536 X0
               have i₂ := b7e241919 X0
               grind)
            | exact superpose b7e241919 b7e1536
            | (have j0 := b7e1536 X0
               have j1 := b7e241919 X0
               grind)
            | (have r₁ := b7e1536 X0
               have r₂ := b7e241919 X0
               grind)
            | exact resolve b7e1536 b7e241919
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e241919
          have b7e242538 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have j0 := b7e242491 X0
               have j1 := b7e1536 X0
               grind)
            | (have r₁ := b7e242491 X0
               have r₂ := b7e1536 X0
               grind)
            | exact resolve b7e242491 b7e1536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1536 b7e242491
          have b7e251272 : ∀ X0 X1 : G, (M.op x X0) = (k y (M.op X1 X0)) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e202734 X0 y x x
               have i₂ := b7e93
               grind)
            | exact superpose b7e93 b7e202734
            | exact resolve b7e202734 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e202734
          have b7e263846 : ∀ X0 X1 : G, (k X1 X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e142559 X0 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e142559
            | (have j0 := b7e142559 X1 X1
               grind)
            | exact resolve b7e142559 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142559
          have b7e264206 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e142564 X0 (σ X0)
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e142564
            | (have j0 := b7e142564 X1 X1
               grind)
            | exact resolve b7e142564 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142564
          have b7e264403 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e33 X0 X0
               have i₂ := b7e264206 (M.op X0 X0) X0
               grind)
            | exact superpose b7e264206 b7e33
            | (have j1 := b7e264206 X0 X0
               grind)
            | exact resolve b7e33 b7e264206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e264206
          have b7e264673 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b7e263846 X0 X0
               have i₂ := b7e264403 X0
               grind)
            | exact superpose b7e264403 b7e263846
            | (have j0 := b7e263846 X0 X0
               have j1 := b7e264403 X0
               grind)
            | exact resolve b7e263846 b7e264403
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e263846 b7e264403
          have b7e264705 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e264673 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e264673
          have b7e286564 : ∀ X0 X1 : G, (k X0 (k y X1)) = (σ (τ (k X0 (M.op x X1)))) ∨ y = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e15 (k X0 (k y X1))
               have i₂ := b7e47279 X1 X0
               grind)
            | exact superpose b7e47279 b7e15
            | (have j1 := b7e47279 X1 X1
               grind)
            | exact resolve b7e15 b7e47279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47279
          have b7e286579 : ∀ X0 X1 : G, (k X0 (M.op x X1)) = (k X0 (k y X1)) ∨ y = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e286564 X0 X1
               have i₂ := b7e15 (k X0 (M.op x X1))
               grind)
            | exact superpose b7e15 b7e286564
            | (have j0 := b7e286564 X0 X1
               grind)
            | exact resolve b7e286564 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e286564
          have b7e286790 : ∀ X0 : G, (k y X0) ≠ (k (k y X0) (M.op x X0)) ∨ (k y X0) = (M.op (k y X0) (k y X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e1244 (k y X0)
               have i₂ := b7e286579 (k y X0) X0
               grind)
            | exact superpose b7e286579 b7e1244
            | (have j0 := b7e1244 (k y X0)
               have j1 := b7e286579 X0 X0
               grind)
            | exact resolve b7e1244 b7e286579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1244 b7e286579
          have b7e286909 : ∀ X0 : G, (k y X0) = (M.op (k y X0) (k y X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b7e286790 X0
               have j1 := b7e47304 X0
               grind)
            | (have r₁ := b7e286790 X0
               have r₂ := b7e47304 X0
               grind)
            | exact resolve b7e286790 b7e47304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47304 b7e286790
          have b7e294071 : ∀ X0 : G, (M.op (k y X0) (k y X0)) = (τ (σ (M.op x X0))) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e14 (M.op (k y X0) (k y X0))
               have i₂ := b7e141322 X0
               grind)
            | exact superpose b7e141322 b7e14
            | (have j1 := b7e141322 X0
               grind)
            | exact resolve b7e14 b7e141322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141322
          have b7e294128 : ∀ X0 : G, (M.op x X0) = (M.op (k y X0) (k y X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e294071 X0
               have i₂ := b7e14 (M.op x X0)
               grind)
            | exact superpose b7e14 b7e294071
            | (have j0 := b7e294071 X0
               grind)
            | exact resolve b7e294071 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294071
          have b7e294330 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (k y X0) X1) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 (k y X0) (k y X0) X1
               have i₂ := b7e294128 X0
               grind)
            | exact superpose b7e294128 b7e35
            | (have j1 := b7e294128 X0
               grind)
            | exact resolve b7e35 b7e294128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294128
          have b7e294359 : ∀ X0 X1 : G, (M.op x X1) = (M.op (k y X0) X1) ∨ y = (M.op x X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e294330 X0 X1
               have i₂ := b7e35 x X0 X1
               grind)
            | exact superpose b7e35 b7e294330
            | (have j0 := b7e294330 X0 X1
               grind)
            | exact resolve b7e294330 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e294330
          have b7e294590 : ∀ X0 : G, (k y X0) = (M.op x (k y X0)) ∨ y = (M.op x X0) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e286909 X0
               have i₂ := b7e294359 X0 (k y X0)
               grind)
            | exact superpose b7e294359 b7e286909
            | (have j0 := b7e286909 X0
               have j1 := b7e294359 X0 x
               grind)
            | exact resolve b7e286909 b7e294359
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e286909 b7e294359
          have b7e294723 : ∀ X0 : G, (k y X0) = (M.op x (k y X0)) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have j0 := b7e294590 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294590
          have b7e316018 : ∀ X0 : G, (σ (M.op y x)) = (σ (k (M.op x X0) x)) ∨ (M.op x X0) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e37582 y X0
               have i₂ := b7e125 X0
               grind)
            | exact superpose b7e125 b7e37582
            | exact resolve b7e37582 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37582
          have b7e316056 : ∀ X0 : G, (σ (M.op x x)) = (σ (k (M.op x X0) x)) ∨ (M.op x X0) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e316018 X0
               have i₂ := b7e125 x
               grind)
            | exact superpose b7e125 b7e316018
            | (have j0 := b7e316018 X0
               grind)
            | exact resolve b7e316018 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e316018
          have b7e316110 : ∀ X0 : G, (σ x) = (σ (k (M.op x X0) x)) ∨ (M.op x X0) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b7e316056 X0
               have i₂ := b7e387
               grind)
            | exact superpose b7e387 b7e316056
            | (have j0 := b7e316056 X0
               grind)
            | exact resolve b7e316056 b7e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e316056
          have b7e316143 : ∀ X0 : G, (M.op x x) = (M.op x X0) ∨ (σ x) = (σ (k (M.op x X0) x)) := by
            intro X0
            first
            | (have i₁ := b7e316110 X0
               have i₂ := b7e125 x
               grind)
            | exact superpose b7e125 b7e316110
            | (have j0 := b7e316110 X0
               grind)
            | exact resolve b7e316110 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e316110
          have b7e316155 : ∀ X0 : G, (σ x) = (σ (k (M.op x X0) x)) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e316143 X0
               have i₂ := b7e387
               grind)
            | exact superpose b7e387 b7e316143
            | (have j0 := b7e316143 X0
               grind)
            | exact resolve b7e316143 b7e387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e387 b7e316143
          have b7e316238 : ∀ X0 : G, (τ (σ x)) = (k (M.op x X0) x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e14 (k (M.op x X0) x)
               have i₂ := b7e316155 X0
               grind)
            | exact superpose b7e316155 b7e14
            | (have j1 := b7e316155 X0
               grind)
            | exact resolve b7e14 b7e316155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e316155
          have b7e316317 : ∀ X0 : G, x = (k (M.op x X0) x) ∨ x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e316238 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e316238
            | (have j0 := b7e316238 X0
               grind)
            | exact resolve b7e316238 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e316238
          have b7e319075 : ∀ X0 : G, x = (k (k y X0) x) ∨ x = (k y X0) ∨ y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e316317 (k y X0)
               have i₂ := b7e294723 X0
               grind)
            | exact superpose b7e294723 b7e316317
            | (have j1 := b7e294723 X0
               grind)
            | exact resolve b7e316317 b7e294723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294723 b7e316317
          have b7e319263 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ y) X0) ∨ x = (k y (τ X0)) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e231350 X0
               have i₂ := b7e319075 (τ X0)
               grind)
            | exact superpose b7e319075 b7e231350
            | (have j0 := b7e231350 X0
               have j1 := b7e319075 (τ X0)
               grind)
            | exact resolve b7e231350 b7e319075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e319075
          have b7e319297 : ∀ X0 : G, x = (k y (τ X0)) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have j0 := b7e319263 X0
               grind)
            | (have r₁ := b7e319263 X0
               have r₂ := b7e124
               grind)
            | exact resolve b7e319263 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e319263
          have b7e618924 : ∀ X0 : G, y = (k x x) ∨ (σ y) = (M.op (σ y) X0) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e231350 X0
               have i₂ := b7e319297 X0
               grind)
            | exact superpose b7e319297 b7e231350
            | (have j0 := b7e231350 X0
               have j1 := b7e319297 X0
               grind)
            | exact resolve b7e231350 b7e319297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e231350 b7e319297
          have b7e618948 : ∀ X0 : G, y = (k x x) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have j0 := b7e618924 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e618924
          have b7e618953 : ∀ X0 : G, y = (M.op x x) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have i₁ := b7e618948 X0
               have i₂ := b7e264705 x
               grind)
            | exact superpose b7e264705 b7e618948
            | (have j0 := b7e618948 X0
               grind)
            | exact resolve b7e618948 b7e264705
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e264705 b7e618948
          have b7e618959 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ y = (M.op x (τ X0)) := by
            intro X0
            first
            | (have j0 := b7e618953 X0
               grind)
            | (have r₁ := b7e618953 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e618953 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e618953
          have b7e619188 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ y)) ∨ y = (M.op x (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X1 X0 (σ y)
               have i₂ := b7e618959 X1
               grind)
            | exact superpose b7e618959 b7e34
            | (have j1 := b7e618959 X1
               grind)
            | exact resolve b7e34 b7e618959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e618959
          have b7e619542 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ x)) ∨ y = (M.op x (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e619188 X0 X1
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e619188
            | (have j0 := b7e619188 X0 X1
               grind)
            | exact resolve b7e619188 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36 b7e619188
          have b7e623204 : ∀ X0 : G, (k X0 (M.op X0 (σ x))) = X0 ∨ y = (M.op x (τ X0)) := by
            intro X0
            grind
          have b7e624405 : ∀ X0 X1 : G, x = (k x y) ∨ y = (k x (τ X0)) ∨ x = y ∨ (M.op X1 X0) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e1812 x (τ X1)
               have i₂ := b7e619542 X0 X1
               grind)
            | exact superpose b7e619542 b7e1812
            | (have j1 := b7e619542 X1 X0
               grind)
            | exact resolve b7e1812 b7e619542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1812 b7e619542
          have b7e624480 : ∀ X0 X1 : G, x = (k x y) ∨ y = (k x (τ X0)) ∨ (M.op X1 X0) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have j0 := b7e624405 X0 X1
               grind)
            | (have r₁ := b7e624405 X0 X1
               have r₂ := b7e124
               grind)
            | exact resolve b7e624405 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e624405
          have b7e625351 : ∀ X0 X1 : G, x = y ∨ y = (k x (τ X0)) ∨ (M.op X1 X0) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e624480 X0 X1
               have i₂ := b7e58
               grind)
            | exact superpose b7e58 b7e624480
            | (have j0 := b7e624480 X0 X1
               grind)
            | exact resolve b7e624480 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e624480
          have b7e625817 : ∀ X0 X1 : G, y = (k x (τ X0)) ∨ (M.op X1 X0) = (M.op X1 (σ x)) := by
            intro X0 X1
            first
            | (have j0 := b7e625351 X0 X1
               grind)
            | (have r₁ := b7e625351 X0 X1
               have r₂ := b7e124
               grind)
            | exact resolve b7e625351 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e625351
          have b7e628992 : y = (M.op x (σ x)) ∨ y = (M.op x (σ x)) ∨ y = (M.op x (τ y)) := by
            first
            | (have i₁ := b7e251272 (σ x) y
               have i₂ := b7e623204 y
               grind)
            | exact superpose b7e623204 b7e251272
            | (have j0 := b7e251272 (σ x) x
               have j1 := b7e623204 y
               grind)
            | exact resolve b7e251272 b7e623204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e251272 b7e623204
          have b7e629062 : y = (M.op x (τ y)) ∨ y = (M.op x (σ x)) := by grind
          clear b7e628992
          have b7e634289 : ∀ X0 : G, y = (k x (τ X0)) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e150
               have i₂ := b7e625817 X0 (σ x)
               grind)
            | (have i₁ := b7e150
               have i₂ := b7e625817 (σ x) (σ x)
               grind)
            | exact superpose b7e625817 b7e150
            | (have j1 := b7e625817 X0 x
               grind)
            | exact resolve b7e150 b7e625817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150 b7e625817
          have b7e635633 : ∀ X0 : G, (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e56913 (τ X0)
               have i₂ := b7e634289 X0
               grind)
            | exact superpose b7e634289 b7e56913
            | (have j0 := b7e56913 (τ X0)
               have j1 := b7e634289 (σ (τ X0))
               grind)
            | exact resolve b7e56913 b7e634289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56913 b7e634289
          have b7e635791 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e635633 X0
               have i₂ := b7e1242
               grind)
            | exact superpose b7e1242 b7e635633
            | (have j0 := b7e635633 X0
               grind)
            | exact resolve b7e635633 b7e1242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1242 b7e635633
          have b7e635901 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (τ X0))) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e635791 X0
               grind)
            | (have r₁ := b7e635791 X0
               have r₂ := b7e123
               grind)
            | exact resolve b7e635791 b7e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123 b7e635791
          have b7e635951 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e635901 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e635901
            | (have j0 := b7e635901 X0
               grind)
            | exact resolve b7e635901 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e635901
          have b7e635952 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b7e635951 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e635951
          have b7e636288 : (τ (σ x)) ≠ (τ (σ x)) ∨ (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
            first
            | (have i₁ := b7e242538 (σ x)
               have i₂ := b7e635952 (σ x)
               grind)
            | exact superpose b7e635952 b7e242538
            | (have j0 := b7e242538 (σ x)
               grind)
            | exact resolve b7e242538 b7e635952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e242538
          have b7e636331 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X1 X0 (σ x)
               have i₂ := b7e635952 X1
               grind)
            | exact superpose b7e635952 b7e34
            | exact resolve b7e34 b7e635952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e635952
          have b7e636658 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by grind
          clear b7e636288
          have b7e636759 : (τ (σ x)) = (M.op (τ (σ x)) (σ x)) := by
            first
            | (have i₁ := b7e636658
               have i₂ := b7e636331 (τ (σ x)) (τ (σ x))
               grind)
            | exact superpose b7e636331 b7e636658
            | exact resolve b7e636658 b7e636331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e636658
          have b7e636857 : x = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e636759
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e636759
            | exact resolve b7e636759 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e636759
          have b7e639749 : y = (M.op x (σ x)) ∨ y = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e629062
               have i₂ := b7e636331 x (τ y)
               grind)
            | exact superpose b7e636331 b7e629062
            | exact resolve b7e629062 b7e636331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e629062 b7e636331
          have b7e640425 : y = (M.op x (σ x)) := by grind
          clear b7e639749
          have b7e640692 : x = y := by
            first
            | (have i₁ := b7e640425
               have i₂ := b7e636857
               grind)
            | exact superpose b7e636857 b7e640425
            | exact resolve b7e640425 b7e636857
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e636857 b7e640425
          have b7e641523 : False := by grind
          exact b7e641523
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b8e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b8e185 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e186 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e185
               have r₂ := b8e24
               grind)
            | exact resolve b8e185 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e187 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e186
            | exact resolve b8e186 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e188 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e187
               grind)
            | exact superpose b8e187 b8e20
            | exact resolve b8e20 b8e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187
          have b8e348 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e188
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
          have b8e349 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e348
          have b8e351 : x = (M.op x y) := by
            first
            | (have r₁ := b8e349
               have r₂ := b8e21
               grind)
            | exact resolve b8e349 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e349
          have b8e353 : False := by grind
          exact b8e353

/-- `Equation3744`: `x ◇ y = (x ◇ z) ◇ (w ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_x_y_pyx_Equation3744 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3744 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3744.models_iff G M).mp hM
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
      have b0e99 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op (M.op X1 X2) (M.op X0 x)) := by
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
      have b0e102 : ∀ X1 : G, (M.op X1 x) = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e99 x X1 x
           have i₂ := b0e11 X1 x x x
           grind)
        | exact superpose b0e11 b0e99
        | exact resolve b0e99 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e99
      have b0e130 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
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
      have b0e331 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e130 (σ x)
           grind)
        | exact superpose b0e130 b0e18
        | exact resolve b0e18 b0e130
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e130
      have b0e335 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e331
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e331
        | exact resolve b0e331 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e331
      have b0e347 : (σ y) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e335
           have i₂ := b0e102 x
           grind)
        | exact superpose b0e102 b0e335
        | exact resolve b0e335 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102 b0e335
      have b0e352 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e347
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e347
        | exact resolve b0e347 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e347
      have b0e353 : False := by grind
      exact b0e353
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : x = (k x y) := by grind
        have b1e47 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e52 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e21
             grind)
          | exact resolve b1e50 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e54 : (σ y) = (σ (k x y)) := by
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
        have b1e55 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e24
             grind)
          | exact superpose b1e24 b1e54
          | exact resolve b1e54 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e54
        have b1e56 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e19
          | exact resolve b1e19 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e22
          | exact resolve b1e22 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e13
          | exact resolve b1e13 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : x = y := by
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
        have b1e64 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e56
          | exact resolve b1e56 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e57
        have b1e65 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e64
          | exact resolve b1e64 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e64
        have b1e66 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e65
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e65
          | exact resolve b1e65 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e67 : False := by grind
        exact b1e67
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
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
        have b2e626 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e627 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e626
             have r₂ := b2e22
             grind)
          | exact resolve b2e626 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e626
        have b2e628 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e627
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e627
          | exact resolve b2e627 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e627
        have b2e629 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e628
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e628
          | exact resolve b2e628 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e628
        have b2e630 : False := by grind
        exact b2e630
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
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
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) = (k (σ x) (σ y)) := by grind
        have b3e25 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e24
          | exact resolve b3e24 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e26 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e25
             grind)
          | exact superpose b3e25 b3e13
          | exact resolve b3e13 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e27 : x = (k x y) := by
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
        have b3e40 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
        have b3e52 : x = (M.op x x) := by
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
        have b3e62 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
        have b3e63 : y = (M.op x x) ∨ y = (k x y) := by grind
        clear b3e62
        have b3e64 : y = (k x y) := by
          first
          | (have r₁ := b3e63
             have r₂ := b3e20
             grind)
          | exact resolve b3e63 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e67 : x = y := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e64
          | exact resolve b3e64 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e64
        have b3e69 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e19
          | exact resolve b3e19 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e73 : (σ x) ≠ (M.op (σ x) (σ x)) := by
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
        have b3e74 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e73
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e73
          | exact resolve b3e73 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e75 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e74
             have i₂ := b3e67
             grind)
          | exact superpose b3e67 b3e74
          | exact resolve b3e74 b3e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67 b3e74
        have b3e76 : False := by grind
        exact b3e76
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X2) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
          have b4e30 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op X0 X1) (M.op X5 X3)) := by
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
          have b4e36 : ∀ X0 X2 X3 : G, (M.op X0 X3) = (M.op (M.op X0 X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e30 X0 x X2 X3 x
               have i₂ := b4e13 X0 X3 x x
               grind)
            | exact superpose b4e13 b4e30
            | exact resolve b4e30 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e42 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 x X1 (M.op x X0) X3
               have i₂ := b4e28 X0 x
               grind)
            | exact superpose b4e28 b4e13
            | exact resolve b4e13 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e43 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b4e42 x X1 x
               have i₂ := b4e13 y X1 x x
               grind)
            | exact superpose b4e13 b4e42
            | exact resolve b4e42 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e112 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e17 (M.op X2 X1) X0
               have i₂ := b4e35 X1 X0 X2
               grind)
            | exact superpose b4e35 b4e17
            | (have j0 := b4e17 (M.op X2 X1) X0
               grind)
            | (have r₁ := b4e17 (M.op X2 X1) X2
               have r₂ := b4e35 X1 X2 X2
               grind)
            | exact resolve b4e17 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e118 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e112 X0 X1 X2
               have i₂ := b4e13 X2 X1 X1 X2
               grind)
            | exact superpose b4e13 b4e112
            | (have j0 := b4e112 X0 X1 X2
               grind)
            | exact resolve b4e112 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e139 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e36 (σ y) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e36
            | exact resolve b4e36 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e172 : y = (k y (M.op x y)) := by grind
          clear b4e43
          have b4e1044 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e2345 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e118 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118
          have b4e6633 : (σ y) ≠ (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e1044 (M.op x y) y
               have i₂ := b4e172
               grind)
            | exact superpose b4e172 b4e1044
            | (have j0 := b4e1044 (M.op x y) y
               grind)
            | exact resolve b4e1044 b4e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6645 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by grind
          clear b4e6633
          have b4e6668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e6645
               have i₂ := b4e139 (σ y)
               grind)
            | exact superpose b4e139 b4e6645
            | exact resolve b4e6645 b4e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6645
          have b4e6688 : (σ y) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have r₁ := b4e6668
               have r₂ := b4e20
               grind)
            | exact resolve b4e6668 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6668
          have b4e6725 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e34 (σ (M.op x y)) (σ y)
               have i₂ := b4e6688
               grind)
            | exact superpose b4e6688 b4e34
            | exact resolve b4e34 b4e6688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e6752 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e2345 (σ (M.op x y)) (σ y)
               have i₂ := b4e6688
               grind)
            | exact superpose b4e6688 b4e2345
            | exact resolve b4e2345 b4e6688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2345 b4e6688
          have b4e6755 : (σ (M.op x y)) = (σ (k y (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e6752
               have i₂ := b4e19 y (M.op x y)
               grind)
            | exact superpose b4e19 b4e6752
            | exact resolve b4e6752 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6752
          have b4e6760 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b4e6725
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e6725
            | exact resolve b4e6725 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6725
          have b4e6767 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b4e6755
               have i₂ := b4e172
               grind)
            | exact superpose b4e172 b4e6755
            | exact resolve b4e6755 b4e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e172 b4e6755
          have b4e6768 : (σ (M.op x y)) = (σ y) := by grind
          clear b4e6767
          have b4e6990 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e1044 y y
               have i₂ := b4e6760
               grind)
            | exact superpose b4e6760 b4e1044
            | (have j0 := b4e1044 y y
               grind)
            | (have r₁ := b4e1044 y y
               have r₂ := b4e6760
               grind)
            | exact resolve b4e1044 b4e6760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1044 b4e6760
          have b4e7012 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e6990
          have b4e7013 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e7012
          have b4e7034 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e7013
               have i₂ := b4e139 (σ y)
               grind)
            | exact superpose b4e139 b4e7013
            | exact resolve b4e7013 b4e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139 b4e7013
          have b4e7976 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e7034
               grind)
            | exact superpose b4e7034 b4e20
            | exact resolve b4e20 b4e7034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7034
          have b4e8019 : False := by grind
          exact b4e8019
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op X1 X0)) := by
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
          have b5e35 : x = (M.op x x) := by
            first
            | (have i₁ := b5e28 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e28
            | exact resolve b5e28 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 X3 : G, (M.op x X1) = (M.op (M.op y X0) (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 x X1 (M.op x X0) X3
               have i₂ := b5e28 X0 x
               grind)
            | exact superpose b5e28 b5e13
            | exact resolve b5e13 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X1 : G, (M.op y X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b5e39 x X1 x
               have i₂ := b5e13 y X1 x x
               grind)
            | exact superpose b5e13 b5e39
            | exact resolve b5e39 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e44 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e47 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e44
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e21
               grind)
            | exact resolve b5e47 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e62 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
          have b5e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b5e66 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e62 X0 X1 X2 x
               have i₂ := b5e33 X2 X0 x
               grind)
            | exact superpose b5e33 b5e62
            | (have j0 := b5e62 X0 X1 X2 x
               grind)
            | exact resolve b5e62 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e72 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e35
               grind)
            | exact superpose b5e35 b5e21
            | exact resolve b5e21 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : x = (k x x) := by grind
          clear b5e35
          have b5e104 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 (M.op X2 X1) X0
               have i₂ := b5e33 X1 X0 X2
               grind)
            | exact superpose b5e33 b5e17
            | (have j0 := b5e17 (M.op X2 X1) X0
               grind)
            | (have r₁ := b5e17 (M.op X2 X1) X2
               have r₂ := b5e33 X1 X2 X2
               grind)
            | exact resolve b5e17 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e110 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e104 X0 X1 X2
               have i₂ := b5e13 X2 X1 X1 X2
               grind)
            | exact superpose b5e13 b5e104
            | (have j0 := b5e104 X0 X1 X2
               grind)
            | exact resolve b5e104 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e177 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b5e26
          have b5e182 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e177 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e177
            | exact resolve b5e177 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e177
          have b5e193 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e308 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = (k X0 (M.op X2 X3)) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X2 X3 X1
               have i₂ := b5e66 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b5e34 X0 X2 X2
               have i₂ := b5e66 X0 (M.op X0 X2) X2
               grind)
            | exact superpose b5e66 b5e34
            | (have j1 := b5e66 (M.op X2 X3) X0 X2
               grind)
            | exact resolve b5e34 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e317 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e344 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e66 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66
          have b5e362 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e308 X0 X1 X2 X3
               have i₂ := b5e34 X2 X3 X0
               grind)
            | exact superpose b5e34 b5e308
            | (have j0 := b5e308 X0 X1 X2 X3
               grind)
            | exact resolve b5e308 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e308
          have b5e383 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e362 X0 X1 X2 X3
               have i₂ := b5e34 X2 X3 X0
               grind)
            | exact superpose b5e34 b5e362
            | (have j0 := b5e362 X0 X1 X2 X3
               grind)
            | exact resolve b5e362 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e362
          have b5e566 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e567 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e566
               have r₂ := b5e24
               grind)
            | exact resolve b5e566 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e566
          have b5e568 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e567
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e567
            | exact resolve b5e567 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e567
          have b5e569 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e568
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e568
            | exact resolve b5e568 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e568
          have b5e574 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e569
               grind)
            | exact superpose b5e569 b5e24
            | exact resolve b5e24 b5e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e579 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b5e32 (σ y) (σ x)
               have i₂ := b5e569
               grind)
            | exact superpose b5e569 b5e32
            | exact resolve b5e32 b5e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e580 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e33 (σ x) X0 (σ y)
               have i₂ := b5e569
               grind)
            | exact superpose b5e569 b5e33
            | exact resolve b5e33 b5e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e585 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e579
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e579
            | exact resolve b5e579 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e579
          have b5e694 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e585
               grind)
            | exact superpose b5e585 b5e14
            | exact resolve b5e14 b5e585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e585
          have b5e696 : y = (k y y) := by
            first
            | (have i₁ := b5e694
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e694
            | exact resolve b5e694 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e694
          have b5e745 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e18 (σ X0) X1
               have i₂ := b5e56 X0 X0
               grind)
            | exact superpose b5e56 b5e18
            | (have j0 := b5e18 (σ X0) X1
               have j1 := b5e56 X0 X0
               grind)
            | exact resolve b5e18 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e753 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33 (σ X0) X2 (σ X1)
               have i₂ := b5e56 X1 X0
               grind)
            | exact superpose b5e56 b5e33
            | (have j1 := b5e56 X1 X0
               grind)
            | exact resolve b5e33 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e791 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e56 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e793 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e791 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e791
          have b5e796 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e745 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e745
          have b5e817 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ (k X0 X0)) = X1 ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e796 X0 X1
               have j1 := b5e344 X1 (σ X0)
               grind)
            | (have r₁ := b5e796 X0 (M.op (σ (k X0 X0)) (σ (k X0 X0)))
               have r₂ := b5e344 X0 (σ (k X0 X0))
               grind)
            | (have r₁ := b5e796 X0 (σ X0)
               have r₂ := b5e344 X0 (σ X0)
               grind)
            | (have r₁ := b5e796 X0 X1
               have r₂ := b5e344 X0 (σ X0)
               grind)
            | exact resolve b5e796 b5e344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e796
          have b5e855 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e696
               grind)
            | exact superpose b5e696 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e856 : y = (M.op y y) := by grind
          clear b5e855
          have b5e859 : y = (M.op x y) := by
            first
            | (have i₁ := b5e856
               have i₂ := b5e40 y
               grind)
            | exact superpose b5e40 b5e856
            | exact resolve b5e856 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e856
          have b5e1453 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e793 (M.op X0 X1)
               have i₂ := b5e32 X0 X1
               grind)
            | exact superpose b5e32 b5e793
            | (have j0 := b5e793 (M.op X0 X1)
               grind)
            | exact resolve b5e793 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1456 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e793 x
               have i₂ := b5e73
               grind)
            | exact superpose b5e73 b5e793
            | (have j0 := b5e793 x
               grind)
            | exact resolve b5e793 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73 b5e793
          have b5e1464 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e1456
          have b5e1465 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b5e1453 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1453
          have b5e1633 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e344 X0 y
               have i₂ := b5e40 y
               grind)
            | exact superpose b5e40 b5e344
            | (have j0 := b5e344 X0 y
               grind)
            | exact resolve b5e344 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e344
          have b5e1638 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b5e1633 X0
               grind)
            | (have r₁ := b5e1633 X0
               have r₂ := b5e859
               grind)
            | exact resolve b5e1633 b5e859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1633
          have b5e2057 : y = (M.op (σ (M.op (τ y) (τ y))) y) ∨ y = (M.op (σ (M.op (τ y) (τ y))) y) := by
            first
            | (have i₁ := b5e182 y
               have i₂ := b5e1638 (σ (M.op (τ y) (τ y)))
               grind)
            | exact superpose b5e1638 b5e182
            | (have j1 := b5e1638 (σ (M.op (τ y) (τ y)))
               grind)
            | exact resolve b5e182 b5e1638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1638
          have b5e2066 : y = (M.op (σ (M.op (τ y) (τ y))) y) := by grind
          clear b5e2057
          have b5e2131 : y ≠ y ∨ (M.op y y) = (σ (M.op (τ y) (τ y))) ∨ (σ (M.op (τ y) (τ y))) = (k y (σ (M.op (τ y) (τ y)))) := by
            first
            | (have i₁ := b5e17 y (σ (M.op (τ y) (τ y)))
               have i₂ := b5e2066
               grind)
            | exact superpose b5e2066 b5e17
            | (have j0 := b5e17 y (σ (M.op (τ y) (τ y)))
               grind)
            | (have r₁ := b5e17 y (σ (M.op (τ y) (τ y)))
               have r₂ := b5e2066
               grind)
            | exact resolve b5e17 b5e2066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2135 : ∀ X0 : G, (M.op y X0) = (M.op (σ (M.op (τ y) (τ y))) X0) := by
            intro X0
            first
            | (have i₁ := b5e34 (σ (M.op (τ y) (τ y))) y X0
               have i₂ := b5e2066
               grind)
            | exact superpose b5e2066 b5e34
            | exact resolve b5e34 b5e2066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2144 : (M.op y y) = (σ (M.op (τ y) (τ y))) ∨ (σ (M.op (τ y) (τ y))) = (k y (σ (M.op (τ y) (τ y)))) := by grind
          clear b5e2131
          have b5e2146 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op (τ y) (τ y))) X0) := by
            intro X0
            first
            | (have i₁ := b5e2135 X0
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e2135
            | exact resolve b5e2135 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2135
          have b5e2148 : (M.op x y) = (σ (M.op (τ y) (τ y))) ∨ (σ (M.op (τ y) (τ y))) = (k y (σ (M.op (τ y) (τ y)))) := by
            first
            | (have i₁ := b5e2144
               have i₂ := b5e40 y
               grind)
            | exact superpose b5e40 b5e2144
            | exact resolve b5e2144 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2144
          have b5e2154 : y = (σ (M.op (τ y) (τ y))) ∨ (σ (M.op (τ y) (τ y))) = (k y (σ (M.op (τ y) (τ y)))) := by
            first
            | (have i₁ := b5e2148
               have i₂ := b5e859
               grind)
            | exact superpose b5e859 b5e2148
            | exact resolve b5e2148 b5e859
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e859 b5e2148
          have b5e2159 : y = (σ (M.op (τ y) (τ y))) ∨ y = (σ (M.op (τ y) (τ y))) := by
            first
            | (have i₁ := b5e2154
               have i₂ := b5e182 y
               grind)
            | exact superpose b5e182 b5e2154
            | exact resolve b5e2154 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2154
          have b5e2160 : y = (σ (M.op (τ y) (τ y))) := by grind
          clear b5e2159
          have b5e2207 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e110 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e110
          have b5e2251 : ∀ X0 : G, (k (M.op (τ y) (τ y)) (τ X0)) = (τ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b5e193 (M.op (τ y) (τ y)) X0
               have i₂ := b5e2160
               grind)
            | exact superpose b5e2160 b5e193
            | exact resolve b5e193 b5e2160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2440 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 (M.op X0 X2)) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e317 (M.op X0 X2) x
               have i₂ := b5e34 X0 X2 x
               grind)
            | exact superpose b5e34 b5e317
            | (have j0 := b5e317 X0 X1
               grind)
            | exact resolve b5e317 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e317
          have b5e3184 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X0 (M.op X1 X2)) ∨ (k X1 (M.op X0 X1)) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            grind
          clear b5e383
          have b5e4655 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e182 (σ X0)
               have i₂ := b5e817 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
               grind)
            | exact superpose b5e817 b5e182
            | (have j1 := b5e817 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
               grind)
            | exact resolve b5e182 b5e817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182 b5e817
          have b5e4688 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have j0 := b5e4655 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4655
          have b5e4713 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e4688 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4688
            | (have j0 := b5e4688 X0
               grind)
            | exact resolve b5e4688 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4688
          have b5e4753 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e4713 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e4713
            | (have j0 := b5e4713 X0
               grind)
            | exact resolve b5e4713 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4713
          have b5e14437 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (τ y) (τ y)))) = (M.op X1 (σ (τ (k y X0)))) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ y) (τ y))) (σ (M.op (τ y) (τ y)))) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e753 (M.op (τ y) (τ y)) (τ X0) X1
               have i₂ := b5e2251 X0
               grind)
            | exact superpose b5e2251 b5e753
            | (have j0 := b5e753 (M.op (τ y) (τ y)) (τ X0) x
               grind)
            | exact resolve b5e753 b5e2251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e753 b5e2251
          have b5e14983 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (τ y) (τ y)))) = (M.op X1 (k y X0)) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ y) (τ y))) (σ (M.op (τ y) (τ y)))) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14437 X0 X1
               have i₂ := b5e15 (k y X0)
               grind)
            | exact superpose b5e15 b5e14437
            | (have j0 := b5e14437 X0 X1
               grind)
            | exact resolve b5e14437 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14437
          have b5e15064 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (k y X0)) ∨ (σ (τ X0)) = (M.op (σ (M.op (τ y) (τ y))) (σ (M.op (τ y) (τ y)))) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14983 X0 X1
               have i₂ := b5e2160
               grind)
            | exact superpose b5e2160 b5e14983
            | (have j0 := b5e14983 X0 X1
               grind)
            | exact resolve b5e14983 b5e2160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e14983
          have b5e15104 : ∀ X0 X1 : G, (σ (τ X0)) = (σ (M.op (τ y) (τ y))) ∨ (M.op X1 y) = (M.op X1 (k y X0)) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15064 X0 X1
               have i₂ := b5e1465 (τ y) (τ y)
               grind)
            | exact superpose b5e1465 b5e15064
            | (have j0 := b5e15064 X0 X1
               grind)
            | exact resolve b5e15064 b5e1465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1465 b5e15064
          have b5e15120 : ∀ X0 X1 : G, (σ (τ X0)) = y ∨ (M.op X1 y) = (M.op X1 (k y X0)) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15104 X0 X1
               have i₂ := b5e2160
               grind)
            | exact superpose b5e2160 b5e15104
            | (have j0 := b5e15104 X0 X1
               grind)
            | exact resolve b5e15104 b5e2160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15104
          have b5e15130 : ∀ X0 X1 : G, y = X0 ∨ (M.op X1 y) = (M.op X1 (k y X0)) ∨ (σ (M.op (τ y) (τ y))) = (M.op (σ (τ X0)) (σ (M.op (τ y) (τ y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15120 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e15120
            | (have j0 := b5e15120 X0 X1
               grind)
            | exact resolve b5e15120 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15120
          have b5e15135 : ∀ X0 X1 : G, y = (M.op (σ (τ X0)) y) ∨ y = X0 ∨ (M.op X1 y) = (M.op X1 (k y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e15130 X0 X1
               have i₂ := b5e2160
               grind)
            | exact superpose b5e2160 b5e15130
            | (have j0 := b5e15130 X0 X1
               grind)
            | exact resolve b5e15130 b5e2160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2160 b5e15130
          have b5e15137 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X1 (k y X0)) ∨ y = X0 ∨ y = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e15135 X0 X1
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e15135
            | (have j0 := b5e15135 X0 X1
               grind)
            | exact resolve b5e15135 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15135
          have b5e131122 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e32 (σ (M.op X0 X0)) (σ X0)
               have i₂ := b5e4753 X0
               grind)
            | exact superpose b5e4753 b5e32
            | (have j1 := b5e4753 X0
               grind)
            | exact resolve b5e32 b5e4753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e131199 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e2207 (σ (M.op X0 X0)) (σ X0)
               have i₂ := b5e4753 X0
               grind)
            | exact superpose b5e4753 b5e2207
            | (have j1 := b5e4753 X0
               grind)
            | exact resolve b5e2207 b5e4753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4753
          have b5e131225 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op X0 X0))) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e131199 X0
               have i₂ := b5e19 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e19 b5e131199
            | (have j0 := b5e131199 X0
               grind)
            | exact resolve b5e131199 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131199
          have b5e131227 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e131122 X0
               have i₂ := b5e19 X0 X0
               grind)
            | exact superpose b5e19 b5e131122
            | (have j0 := b5e131122 X0
               grind)
            | exact resolve b5e131122 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131122
          have b5e131429 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          clear b5e131225
          have b5e131430 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b5e131429 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131429
          have b5e132728 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14 (k X0 X0)
               have i₂ := b5e131227 X0
               grind)
            | exact superpose b5e131227 b5e14
            | (have j1 := b5e131227 X0
               grind)
            | exact resolve b5e14 b5e131227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131227
          have b5e132982 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e132728 X0
               have i₂ := b5e14 (M.op X0 X0)
               grind)
            | exact superpose b5e14 b5e132728
            | (have j0 := b5e132728 X0
               grind)
            | exact resolve b5e132728 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132728
          have b5e163590 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (σ X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e132982 X0
               have i₂ := b5e131430 X0
               grind)
            | exact superpose b5e131430 b5e132982
            | (have j0 := b5e132982 X0
               have j1 := b5e131430 X0
               grind)
            | exact resolve b5e132982 b5e131430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131430 b5e132982
          have b5e163831 : ∀ X0 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e163590 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e163590
          have b5e174555 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op (σ y) X0)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2440 (σ y) (σ x) x
               have i₂ := b5e569
               grind)
            | exact superpose b5e569 b5e2440
            | exact resolve b5e2440 b5e569
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e569 b5e2440
          have b5e175366 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b5e174555 X0
               grind)
            | (have r₁ := b5e174555 X0
               have r₂ := b5e574
               grind)
            | exact resolve b5e174555 b5e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e174555
          have b5e175552 : ∀ X0 : G, (σ x) = (σ (k x y)) ∨ (σ y) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e175366 X0
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e175366
            | (have j0 := b5e175366 X0
               grind)
            | exact resolve b5e175366 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175366
          have b5e175645 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e175552 X0
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e175552
            | (have j0 := b5e175552 X0
               grind)
            | exact resolve b5e175552 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e175552
          have b5e175675 : ∀ X0 : G, (σ y) = (k (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have j0 := b5e175645 X0
               grind)
            | (have r₁ := b5e175645 X0
               have r₂ := b5e574
               grind)
            | exact resolve b5e175645 b5e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e175645
          have b5e179938 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e175675 (σ x)
               have i₂ := b5e3184 (σ y) (σ x) X0
               grind)
            | exact superpose b5e3184 b5e175675
            | (have j1 := b5e3184 (σ y) (σ x) X0
               grind)
            | exact resolve b5e175675 b5e3184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3184 b5e175675
          have b5e180260 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e179938 X0
               grind)
            | (have r₁ := b5e179938 X0
               have r₂ := b5e574
               grind)
            | exact resolve b5e179938 b5e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e179938
          have b5e180505 : ∀ X0 : G, (M.op (σ x) (σ x)) = (k (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e180260 X0
               have i₂ := b5e580 (σ x)
               grind)
            | exact superpose b5e580 b5e180260
            | exact resolve b5e180260 b5e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180260
          have b5e180639 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e180505 X0
               have i₂ := b5e1464
               grind)
            | exact superpose b5e1464 b5e180505
            | exact resolve b5e180505 b5e1464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1464 b5e180505
          have b5e180729 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e180639 X0
               have i₂ := b5e580 (σ x)
               grind)
            | exact superpose b5e580 b5e180639
            | (have j0 := b5e180639 X0
               grind)
            | exact resolve b5e180639 b5e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e580 b5e180639
          have b5e180768 : ∀ X0 : G, (σ x) = (k (σ y) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e180729 X0
               grind)
            | (have r₁ := b5e180729 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e180729 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180729
          have b5e180946 : ∀ X0 : G, (τ (σ x)) = (k y (τ (M.op (σ x) X0))) := by
            intro X0
            first
            | (have i₁ := b5e193 y (M.op (σ x) X0)
               have i₂ := b5e180768 X0
               grind)
            | exact superpose b5e180768 b5e193
            | exact resolve b5e193 b5e180768
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e193 b5e180768
          have b5e181102 : ∀ X0 : G, x = (k y (τ (M.op (σ x) X0))) := by
            intro X0
            first
            | (have i₁ := b5e180946 X0
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e180946
            | exact resolve b5e180946 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180946
          have b5e224474 : ∀ X0 : G, (M.op (σ (M.op (τ y) (τ y))) y) = (M.op x (k y X0)) ∨ y = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e2146 (k y X0)
               have i₂ := b5e15137 X0 (σ (M.op (τ y) (τ y)))
               grind)
            | exact superpose b5e15137 b5e2146
            | (have j1 := b5e15137 X0 x
               grind)
            | exact resolve b5e2146 b5e15137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2146 b5e15137
          have b5e224586 : ∀ X0 : G, y = (M.op x (k y X0)) ∨ y = X0 ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e224474 X0
               have i₂ := b5e2066
               grind)
            | exact superpose b5e2066 b5e224474
            | (have j0 := b5e224474 X0
               grind)
            | exact resolve b5e224474 b5e2066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2066 b5e224474
          have b5e224621 : ∀ X0 : G, y = (M.op x x) ∨ y = (τ (M.op (σ x) X0)) ∨ y = (M.op (τ (M.op (σ x) X0)) y) := by
            intro X0
            first
            | (have i₁ := b5e224586 (τ (M.op (σ x) X0))
               have i₂ := b5e181102 X0
               grind)
            | exact superpose b5e181102 b5e224586
            | (have j0 := b5e224586 (τ (M.op (σ x) X0))
               grind)
            | exact resolve b5e224586 b5e181102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e224586
          have b5e224777 : ∀ X0 : G, y = (M.op (τ (M.op (σ x) X0)) y) ∨ y = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e224621 X0
               grind)
            | (have r₁ := b5e224621 X0
               have r₂ := b5e21
               grind)
            | exact resolve b5e224621 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e224621
          have b5e225078 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k y (τ (M.op (σ x) X0))) ∨ y = (τ (M.op (σ x) X0)) ∨ y = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e2207 (τ (M.op (σ x) X0)) y
               have i₂ := b5e224777 X0
               grind)
            | exact superpose b5e224777 b5e2207
            | (have j1 := b5e224777 X0
               grind)
            | exact resolve b5e2207 b5e224777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2207 b5e224777
          have b5e225089 : ∀ X0 : G, (τ (M.op (σ x) X0)) = (k y (τ (M.op (σ x) X0))) ∨ y = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e225078 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225078
          have b5e225095 : ∀ X0 : G, y = (τ (M.op (σ x) X0)) ∨ x = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e225089 X0
               have i₂ := b5e181102 X0
               grind)
            | exact superpose b5e181102 b5e225089
            | (have j0 := b5e225089 X0
               grind)
            | exact resolve b5e225089 b5e181102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225089
          have b5e225231 : ∀ X0 : G, x = (k y y) ∨ x = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e181102 X0
               have i₂ := b5e225095 X0
               grind)
            | exact superpose b5e225095 b5e181102
            | (have j1 := b5e225095 X0
               grind)
            | exact resolve b5e181102 b5e225095
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e181102 b5e225095
          have b5e225346 : ∀ X0 : G, x = y ∨ x = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e225231 X0
               have i₂ := b5e696
               grind)
            | exact superpose b5e696 b5e225231
            | (have j0 := b5e225231 X0
               grind)
            | exact resolve b5e225231 b5e696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225231
          have b5e225369 : ∀ X0 : G, x = (τ (M.op (σ x) X0)) := by
            intro X0
            first
            | (have j0 := b5e225346 X0
               grind)
            | (have r₁ := b5e225346 X0
               have r₂ := b5e72
               grind)
            | exact resolve b5e225346 b5e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225346
          have b5e225566 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e15 (M.op (σ x) X0)
               have i₂ := b5e225369 X0
               grind)
            | exact superpose b5e225369 b5e15
            | exact resolve b5e15 b5e225369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225369
          have b5e226016 : ∀ X0 : G, (M.op y X0) = (M.op x (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 (σ x)
               have i₂ := b5e225566 X0
               grind)
            | exact superpose b5e225566 b5e28
            | exact resolve b5e28 b5e225566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e225566
          have b5e226476 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e226016 X0
               have i₂ := b5e226016 X1
               grind)
            | exact superpose b5e226016 b5e226016
            | exact resolve b5e226016 b5e226016
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e226016
          have b5e227149 : ∀ X0 : G, (σ y) = (σ (M.op y X0)) ∨ (M.op y X0) = (k y y) := by
            intro X0
            first
            | (have i₁ := b5e163831 y
               have i₂ := b5e226476 y x
               grind)
            | (have i₁ := b5e163831 y
               have i₂ := b5e226476 X0 y
               grind)
            | exact superpose b5e226476 b5e163831
            | exact resolve b5e163831 b5e226476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e163831
          have b5e227335 : ∀ X0 X1 : G, (M.op y X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e40 X1
               have i₂ := b5e226476 X1 X0
               grind)
            | (have i₁ := b5e40 X1
               have i₂ := b5e226476 X0 X1
               grind)
            | exact superpose b5e226476 b5e40
            | exact resolve b5e40 b5e226476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e227537 : ∀ X0 : G, x = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e226476 x X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e226476 X0 x
               grind)
            | exact superpose b5e226476 b5e22
            | exact resolve b5e22 b5e226476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e226476
          have b5e227640 : ∀ X1 : G, x = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b5e227335 x X1
               have i₂ := b5e227537 x
               grind)
            | exact superpose b5e227537 b5e227335
            | exact resolve b5e227335 b5e227537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227335
          have b5e227721 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) ∨ (M.op y X0) = (k y y) := by
            intro X0
            first
            | (have i₁ := b5e227149 X0
               have i₂ := b5e40 X0
               grind)
            | exact superpose b5e40 b5e227149
            | (have j0 := b5e227149 X0
               grind)
            | exact resolve b5e227149 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e227149
          have b5e227880 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op y X0) = (k y y) := by
            intro X0
            first
            | (have i₁ := b5e227721 X0
               have i₂ := b5e227640 X0
               grind)
            | exact superpose b5e227640 b5e227721
            | (have j0 := b5e227721 X0
               grind)
            | exact resolve b5e227721 b5e227640
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227640 b5e227721
          have b5e228010 : ∀ X0 : G, (M.op y X0) = (k y y) := by
            intro X0
            first
            | (have j0 := b5e227880 X0
               grind)
            | (have r₁ := b5e227880 X0
               have r₂ := b5e574
               grind)
            | exact resolve b5e227880 b5e574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e574 b5e227880
          have b5e228138 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e228010 X0
               have i₂ := b5e696
               grind)
            | exact superpose b5e696 b5e228010
            | exact resolve b5e228010 b5e696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e696 b5e228010
          have b5e228237 : x = y := by
            first
            | (have i₁ := b5e228138 x
               have i₂ := b5e227537 x
               grind)
            | exact superpose b5e227537 b5e228138
            | exact resolve b5e228138 b5e227537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e227537 b5e228138
          have b5e228323 : False := by grind
          exact b5e228323
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
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
        have b6e92 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
        have b6e104 : x = (M.op y x) ∨ y = (M.op x x) := by grind
        clear b6e92
        have b6e112 : y = (M.op x x) := by
          first
          | (have r₁ := b6e104
             have r₂ := b6e21
             grind)
          | exact resolve b6e104 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e121 : False := by grind
        exact b6e121
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
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
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
          have b7e28 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op X1 X0)) := by
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
          have b7e46 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e48 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X2 X1) (M.op X2 X1)) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 (M.op X2 X1) X0
               have i₂ := b7e33 X1 X0 X2
               grind)
            | exact superpose b7e33 b7e17
            | (have j0 := b7e17 (M.op X2 X1) X0
               grind)
            | (have r₁ := b7e17 (M.op X2 X1) X2
               have r₂ := b7e33 X1 X2 X2
               grind)
            | exact resolve b7e17 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e50 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X1) ∨ (M.op X2 X1) = X0 ∨ (k (M.op X2 X1) X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e48 X0 X1 X2
               have i₂ := b7e13 X2 X1 X1 X2
               grind)
            | exact superpose b7e13 b7e48
            | (have j0 := b7e48 X0 X1 X2
               grind)
            | exact resolve b7e48 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e52 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e14
            | exact resolve b7e14 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : y = (k x y) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e56
            | exact resolve b7e56 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b7e70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X2) = (M.op X0 (M.op X3 X2)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
          have b7e76 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e70 X0 X1 X2 x
               have i₂ := b7e33 X2 X0 x
               grind)
            | exact superpose b7e33 b7e70
            | (have j0 := b7e70 X0 X1 X2 x
               grind)
            | exact resolve b7e70 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e89 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e90 : y = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b7e89
               have r₂ := b7e21
               grind)
            | exact resolve b7e89 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e92 : y = (M.op y x) := by
            first
            | (have r₁ := b7e90
               have r₂ := b7e22
               grind)
            | exact resolve b7e90 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e94 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ y) (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e122 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e22
            | exact resolve b7e22 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e124 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e33 x X0 y
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e33
            | exact resolve b7e33 b7e92
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
          have b7e154 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e28 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e28
            | exact resolve b7e28 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e178 : y = (k y (M.op y x)) := by grind
          have b7e191 : y = (k y y) := by
            first
            | (have i₁ := b7e178
               have i₂ := b7e92
               grind)
            | exact superpose b7e92 b7e178
            | exact resolve b7e178 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178
          have b7e225 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e32 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e232 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e225
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e225
            | exact resolve b7e225 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e225
          have b7e236 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e232
               grind)
            | exact superpose b7e232 b7e14
            | exact resolve b7e14 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e238 : x = (k x x) := by
            first
            | (have i₁ := b7e236
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e236
            | exact resolve b7e236 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e236
          have b7e259 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e238
               grind)
            | exact superpose b7e238 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e238
          have b7e260 : x = (M.op x x) := by grind
          clear b7e259
          have b7e294 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = (k X0 (M.op X2 X3)) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e34 X2 X3 X1
               have i₂ := b7e76 (M.op X2 X3) X0 X1
               grind)
            | (have i₁ := b7e34 X0 X2 X2
               have i₂ := b7e76 X0 (M.op X0 X2) X2
               grind)
            | exact superpose b7e76 b7e34
            | (have j1 := b7e76 (M.op X2 X3) X0 X2
               grind)
            | exact resolve b7e34 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e322 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X1) X2) = (M.op (σ X0) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e19 X1 X0
               have i₂ := b7e76 (σ X0) (σ X1) X2
               grind)
            | exact superpose b7e76 b7e19
            | (have j1 := b7e76 (σ X1) (σ X0) X2
               grind)
            | exact resolve b7e19 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e326 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e76 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e344 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op (M.op X2 X3) X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e294 X0 X1 X2 X3
               have i₂ := b7e34 X2 X3 X0
               grind)
            | exact superpose b7e34 b7e294
            | (have j0 := b7e294 X0 X1 X2 X3
               grind)
            | exact resolve b7e294 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e294
          have b7e369 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k X0 (M.op X2 X3)) ∨ (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X0) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e344 X0 X1 X2 X3
               have i₂ := b7e34 X2 X3 X0
               grind)
            | exact superpose b7e34 b7e344
            | (have j0 := b7e344 X0 X1 X2 X3
               grind)
            | exact resolve b7e344 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e344
          have b7e393 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e154
               grind)
            | exact superpose b7e154 b7e23
            | exact resolve b7e23 b7e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e610 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e64 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e612 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e610 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e610
          have b7e780 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
            intro X0
            first
            | (have i₁ := b7e26 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
               have i₂ := b7e134 (τ X0)
               grind)
            | exact superpose b7e134 b7e26
            | exact resolve b7e26 b7e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e792 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e780 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e780
            | exact resolve b7e780 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e780
          have b7e806 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b7e823 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e806 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e806
            | exact resolve b7e806 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e806
          have b7e923 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
            intro X0
            first
            | (have i₁ := b7e141 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
               have i₂ := b7e823 (σ X0)
               grind)
            | exact superpose b7e823 b7e141
            | exact resolve b7e141 b7e823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141 b7e823
          have b7e940 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e923 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e923
            | exact resolve b7e923 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e923
          have b7e1232 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e612 y
               have i₂ := b7e191
               grind)
            | exact superpose b7e191 b7e612
            | (have j0 := b7e612 y
               grind)
            | exact resolve b7e612 b7e191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e191 b7e612
          have b7e1238 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b7e1232
          have b7e1244 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1238
               have i₂ := b7e94 (σ y)
               grind)
            | exact superpose b7e94 b7e1238
            | exact resolve b7e1238 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e1238
          have b7e1417 : ∀ X0 : G, y ≠ (M.op y x) ∨ (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e326 X0 y
               have i₂ := b7e124 y
               grind)
            | exact superpose b7e124 b7e326
            | (have j0 := b7e326 X0 y
               grind)
            | exact resolve b7e326 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1424 : ∀ X0 : G, x ≠ x ∨ (k x X0) = (M.op X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e326 X0 x
               have i₂ := b7e260
               grind)
            | exact superpose b7e260 b7e326
            | (have j0 := b7e326 X0 x
               grind)
            | (have r₁ := b7e326 X0 x
               have r₂ := b7e260
               grind)
            | exact resolve b7e326 b7e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e326
          have b7e1425 : ∀ X0 : G, (k x X0) = (M.op X0 x) ∨ x = (M.op X0 x) := by
            intro X0
            first
            | (have j0 := b7e1424 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1424
          have b7e1433 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b7e1417 X0
               grind)
            | (have r₁ := b7e1417 X0
               have r₂ := b7e92
               grind)
            | exact resolve b7e1417 b7e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92 b7e1417
          have b7e1437 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e1433 X0
               have i₂ := b7e124 X0
               grind)
            | exact superpose b7e124 b7e1433
            | (have j0 := b7e1433 X0
               grind)
            | exact resolve b7e1433 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1433
          have b7e1440 : ∀ X0 : G, (k y X0) = (M.op X0 x) ∨ y = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e1437 X0
               have i₂ := b7e124 X0
               grind)
            | exact superpose b7e124 b7e1437
            | (have j0 := b7e1437 X0
               grind)
            | exact resolve b7e1437 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1437
          have b7e1741 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e50 X0 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e2589 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) X0) ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e133 (M.op (σ X0) X1) X0
               have i₂ := b7e1741 (σ X0) X1
               grind)
            | exact superpose b7e1741 b7e133
            | (have j1 := b7e1741 (σ X0) X1
               grind)
            | exact resolve b7e133 b7e1741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e2595 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) X0) = X0 ∨ (σ X0) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e2589 X0 X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e2589
            | (have j0 := b7e2589 X0 X1
               grind)
            | exact resolve b7e2589 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2589
          have b7e2765 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 (M.op X0 X2)) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b7e369 X1 X1 X0 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e369
          have b7e4771 : y = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) ∨ y = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) := by
            first
            | (have i₁ := b7e1440 (σ (σ (M.op (τ (τ y)) (τ (τ y)))))
               have i₂ := b7e792 y
               grind)
            | exact superpose b7e792 b7e1440
            | (have j0 := b7e1440 (σ (σ (M.op (τ (τ y)) (τ (τ y)))))
               grind)
            | exact resolve b7e1440 b7e792
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e792 b7e1440
          have b7e4772 : y = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) := by grind
          clear b7e4771
          have b7e5242 : x = (M.op (τ (τ (M.op (σ (σ x)) (σ (σ x))))) x) ∨ x = (M.op (τ (τ (M.op (σ (σ x)) (σ (σ x))))) x) := by
            first
            | (have i₁ := b7e1425 (τ (τ (M.op (σ (σ x)) (σ (σ x)))))
               have i₂ := b7e940 x
               grind)
            | exact superpose b7e940 b7e1425
            | (have j0 := b7e1425 (τ (τ (M.op (σ (σ x)) (σ (σ x)))))
               grind)
            | exact resolve b7e1425 b7e940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1425
          have b7e5245 : x = (M.op (τ (τ (M.op (σ (σ x)) (σ (σ x))))) x) := by grind
          clear b7e5242
          have b7e5888 : ∀ X0 : G, (M.op y X0) = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) X0) := by
            intro X0
            first
            | (have i₁ := b7e34 (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x X0
               have i₂ := b7e4772
               grind)
            | exact superpose b7e4772 b7e34
            | exact resolve b7e34 b7e4772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e8179 : (τ (τ (M.op (σ (σ x)) (σ (σ x))))) = (k x (τ (τ (M.op (σ (σ x)) (σ (σ x)))))) ∨ x = (τ (τ (M.op (σ (σ x)) (σ (σ x))))) := by
            first
            | (have i₁ := b7e1741 (τ (τ (M.op (σ (σ x)) (σ (σ x))))) x
               have i₂ := b7e5245
               grind)
            | exact superpose b7e5245 b7e1741
            | exact resolve b7e1741 b7e5245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1741 b7e5245
          have b7e8186 : x = (τ (τ (M.op (σ (σ x)) (σ (σ x))))) ∨ x = (τ (τ (M.op (σ (σ x)) (σ (σ x))))) := by
            first
            | (have i₁ := b7e8179
               have i₂ := b7e940 x
               grind)
            | exact superpose b7e940 b7e8179
            | exact resolve b7e8179 b7e940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e940 b7e8179
          have b7e8187 : x = (τ (τ (M.op (σ (σ x)) (σ (σ x))))) := by grind
          clear b7e8186
          have b7e8501 : ∀ X0 : G, (σ x) = (M.op (σ X0) (σ x)) ∨ (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e154
               have i₂ := b7e322 X0 x (σ x)
               grind)
            | (have i₁ := b7e154
               have i₂ := b7e322 x x (σ x)
               grind)
            | exact superpose b7e322 b7e154
            | (have j1 := b7e322 X0 x x
               grind)
            | exact resolve b7e154 b7e322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154 b7e322
          have b7e8588 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e8501 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8501
          have b7e8771 : ∀ X0 : G, (σ (k x X0)) = (k (τ (M.op (σ (σ x)) (σ (σ x)))) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e26 (τ (M.op (σ (σ x)) (σ (σ x)))) X0
               have i₂ := b7e8187
               grind)
            | exact superpose b7e8187 b7e26
            | exact resolve b7e26 b7e8187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e8187
          have b7e63388 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x X0))) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e28 (σ x) (σ X0)
               have i₂ := b7e8588 X0
               grind)
            | exact superpose b7e8588 b7e28
            | (have j1 := b7e8588 X0
               grind)
            | exact resolve b7e28 b7e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28 b7e8588
          have b7e63446 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ (k x X0))) ∨ (σ x) = (M.op (σ X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e63388 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e63388
            | (have j0 := b7e63388 X0
               grind)
            | exact resolve b7e63388 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63388
          have b7e66478 : ∀ X0 X1 : G, x ≠ x ∨ (M.op X0 x) = (k x (M.op X0 X1)) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b7e2765 X0 x X1
               have i₂ := b7e260
               grind)
            | exact superpose b7e260 b7e2765
            | (have j0 := b7e2765 X0 x X1
               grind)
            | (have r₁ := b7e2765 X0 x x
               have r₂ := b7e260
               grind)
            | exact resolve b7e2765 b7e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e260 b7e2765
          have b7e66479 : ∀ X0 X1 : G, (M.op X0 x) = (k x (M.op X0 X1)) ∨ x = (M.op X0 x) := by
            intro X0 X1
            first
            | (have j0 := b7e66478 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66478
          have b7e66585 : ∀ X0 : G, (k x (M.op y X0)) = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) ∨ x = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) := by
            intro X0
            first
            | (have i₁ := b7e66479 (σ (σ (M.op (τ (τ y)) (τ (τ y))))) X0
               have i₂ := b7e5888 X0
               grind)
            | exact superpose b7e5888 b7e66479
            | (have j0 := b7e66479 (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x
               grind)
            | exact resolve b7e66479 b7e5888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e5888 b7e66479
          have b7e66741 : ∀ X0 : G, y = (k x (M.op y X0)) ∨ x = (M.op (σ (σ (M.op (τ (τ y)) (τ (τ y))))) x) := by
            intro X0
            first
            | (have i₁ := b7e66585 X0
               have i₂ := b7e4772
               grind)
            | exact superpose b7e4772 b7e66585
            | exact resolve b7e66585 b7e4772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66585
          have b7e66748 : ∀ X0 : G, x = y ∨ y = (k x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e66741 X0
               have i₂ := b7e4772
               grind)
            | exact superpose b7e4772 b7e66741
            | (have j0 := b7e66741 X0
               grind)
            | exact resolve b7e66741 b7e4772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4772 b7e66741
          have b7e66754 : ∀ X0 : G, y = (k x (M.op y X0)) := by
            intro X0
            first
            | (have j0 := b7e66748 X0
               grind)
            | (have r₁ := b7e66748 X0
               have r₂ := b7e122
               grind)
            | exact resolve b7e66748 b7e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e122 b7e66748
          have b7e266449 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op y X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e63446 (M.op y X0)
               have i₂ := b7e66754 X0
               grind)
            | exact superpose b7e66754 b7e63446
            | (have j0 := b7e63446 (M.op y X0)
               grind)
            | exact resolve b7e63446 b7e66754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63446
          have b7e266574 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ x) = (M.op (σ (M.op y X0)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e266449 X0
               have i₂ := b7e1244
               grind)
            | exact superpose b7e1244 b7e266449
            | (have j0 := b7e266449 X0
               grind)
            | exact resolve b7e266449 b7e1244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266449
          have b7e266581 : ∀ X0 : G, (σ x) = (M.op (σ (M.op y X0)) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e266574 X0
               grind)
            | (have r₁ := b7e266574 X0
               have r₂ := b7e393
               grind)
            | exact resolve b7e266574 b7e393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266574
          have b7e266729 : ∀ X0 : G, (M.op y X0) = (k (τ (σ x)) (M.op y X0)) ∨ (σ x) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e2595 (M.op y X0) (σ x)
               have i₂ := b7e266581 X0
               grind)
            | exact superpose b7e266581 b7e2595
            | exact resolve b7e2595 b7e266581
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2595 b7e266581
          have b7e266790 : ∀ X0 : G, (M.op y X0) = (k x (M.op y X0)) ∨ (σ x) = (σ (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b7e266729 X0
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e266729
            | (have j0 := b7e266729 X0
               grind)
            | exact resolve b7e266729 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266729
          have b7e266825 : ∀ X0 : G, (σ x) = (σ (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e266790 X0
               have i₂ := b7e66754 X0
               grind)
            | exact superpose b7e66754 b7e266790
            | (have j0 := b7e266790 X0
               grind)
            | exact resolve b7e266790 b7e66754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266790
          have b7e267447 : ∀ X0 : G, (k (τ (M.op (σ (σ x)) (σ (σ x)))) (σ x)) = (σ (k x (M.op y X0))) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e8771 (M.op y X0)
               have i₂ := b7e266825 X0
               grind)
            | exact superpose b7e266825 b7e8771
            | (have j1 := b7e266825 X0
               grind)
            | exact resolve b7e8771 b7e266825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266825
          have b7e267479 : ∀ X0 : G, (σ y) = (k (τ (M.op (σ (σ x)) (σ (σ x)))) (σ x)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e267447 X0
               have i₂ := b7e66754 X0
               grind)
            | exact superpose b7e66754 b7e267447
            | (have j0 := b7e267447 X0
               grind)
            | exact resolve b7e267447 b7e66754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66754 b7e267447
          have b7e267512 : ∀ X0 : G, (σ y) = (σ (k x x)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e267479 X0
               have i₂ := b7e8771 x
               grind)
            | exact superpose b7e8771 b7e267479
            | (have j0 := b7e267479 X0
               grind)
            | exact resolve b7e267479 b7e8771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e8771 b7e267479
          have b7e267523 : ∀ X0 : G, (σ x) = (σ y) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e267512 X0
               have i₂ := b7e232
               grind)
            | exact superpose b7e232 b7e267512
            | (have j0 := b7e267512 X0
               grind)
            | exact resolve b7e267512 b7e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e232 b7e267512
          have b7e267527 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b7e267523 X0
               grind)
            | (have r₁ := b7e267523 X0
               have r₂ := b7e393
               grind)
            | exact resolve b7e267523 b7e393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e393 b7e267523
          have b7e267658 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e33 X1 X0 y
               have i₂ := b7e267527 X1
               grind)
            | exact superpose b7e267527 b7e33
            | exact resolve b7e33 b7e267527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33 b7e267527
          have b7e269030 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e267658 (σ x) (σ x)
               grind)
            | exact superpose b7e267658 b7e23
            | exact resolve b7e23 b7e267658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e269034 : (σ y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b7e1244
               have i₂ := b7e267658 (σ x) (σ y)
               grind)
            | exact superpose b7e267658 b7e1244
            | exact resolve b7e1244 b7e267658
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1244 b7e267658
          have b7e269792 : (σ y) = (M.op (σ x) x) := by
            first
            | (have i₁ := b7e269034
               have i₂ := b7e124 (σ x)
               grind)
            | exact superpose b7e124 b7e269034
            | exact resolve b7e269034 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e269034
          have b7e269794 : (σ y) ≠ (M.op (σ x) x) := by
            first
            | (have i₁ := b7e269030
               have i₂ := b7e124 (σ x)
               grind)
            | exact superpose b7e124 b7e269030
            | exact resolve b7e269030 b7e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124 b7e269030
          have b7e270704 : False := by grind
          exact b7e270704
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
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b8e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e73 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X1 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
          have b8e75 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 X2) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e31 X2 X1 X2
               have i₂ := b8e18 X2 X0
               grind)
            | (have i₁ := b8e31 X1 X2 x
               have i₂ := b8e18 X0 (M.op x X1)
               grind)
            | exact superpose b8e18 b8e31
            | (have j1 := b8e18 X2 X0
               grind)
            | exact resolve b8e31 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op X0 (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
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
          have b8e101 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
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
          have b8e106 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e101 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e101
            | exact resolve b8e101 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e101
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
          have b8e139 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e18 X0 (σ (M.op (τ X0) (τ X0)))
               have i₂ := b8e106 X0
               grind)
            | exact superpose b8e106 b8e18
            | (have j0 := b8e18 X0 (σ (M.op (τ X0) (τ X0)))
               grind)
            | exact resolve b8e18 b8e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e142 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have j0 := b8e139 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e167 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          have b8e181 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e167 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e167
            | exact resolve b8e167 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167
          have b8e185 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e186 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e185
               have r₂ := b8e24
               grind)
            | exact resolve b8e185 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e185
          have b8e187 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e186
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e186
            | exact resolve b8e186 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e188 : (σ x) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e187
               grind)
            | exact superpose b8e187 b8e24
            | exact resolve b8e24 b8e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e190 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b8e32 (σ y) (σ x) X0
               have i₂ := b8e187
               grind)
            | exact superpose b8e187 b8e32
            | exact resolve b8e32 b8e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e192 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (k x y))) := by
            intro X0
            first
            | (have i₁ := b8e31 (σ x) X0 (σ y)
               have i₂ := b8e187
               grind)
            | exact superpose b8e187 b8e31
            | exact resolve b8e31 b8e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e187
          have b8e224 : (σ x) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e188
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
          have b8e225 : (σ x) ≠ (σ (M.op y x)) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e224
               have r₂ := b8e21
               grind)
            | exact resolve b8e224 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224
          have b8e227 : (σ x) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b8e225
               have r₂ := b8e22
               grind)
            | exact resolve b8e225 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225
          have b8e274 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e18 (σ X0) X1
               have i₂ := b8e71 X0 X0
               grind)
            | exact superpose b8e71 b8e18
            | (have j0 := b8e18 (σ X0) X1
               have j1 := b8e71 X0 X0
               grind)
            | exact resolve b8e18 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e300 : ∀ X0 X1 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) (σ X1)
               have i₂ := b8e71 X0 X1
               grind)
            | exact superpose b8e71 b8e30
            | (have j1 := b8e71 X0 X1
               grind)
            | exact resolve b8e30 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e306 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e71 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e307 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e308 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e306 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e306
          have b8e311 : ∀ X0 X1 : G, (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X0)) = X1 ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e274 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274
          have b8e316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e300 X0 X1
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e300
            | (have j0 := b8e300 X0 X1
               grind)
            | exact resolve b8e300 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e300
          have b8e428 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) := by
            intro X0
            first
            | (have i₁ := b8e113 X0 (τ (M.op (σ (σ X0)) (σ (σ X0))))
               have i₂ := b8e181 (σ X0)
               grind)
            | exact superpose b8e181 b8e113
            | exact resolve b8e113 b8e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113 b8e181
          have b8e443 : ∀ X0 : G, (k X0 (τ (τ (M.op (σ (σ X0)) (σ (σ X0)))))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e428 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e428
            | exact resolve b8e428 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e428
          have b8e483 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
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
          have b8e515 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e483 X0
               grind)
            | (have r₁ := b8e483 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e483 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e483
          have b8e526 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op y x)) X0) := by
            intro X0
            first
            | (have j0 := b8e515 X0
               grind)
            | (have r₁ := b8e515 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e515 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e515
          have b8e580 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b8e192 X0
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e192
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e192 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e620 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) ∨ x = (M.op y x) := by
            intro X0
            first
            | (have j0 := b8e580 X0
               grind)
            | (have r₁ := b8e580 X0
               have r₂ := b8e21
               grind)
            | exact resolve b8e580 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e580
          have b8e635 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y x))) := by
            intro X0
            first
            | (have j0 := b8e620 X0
               grind)
            | (have r₁ := b8e620 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e620 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e620
          have b8e821 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e308 (M.op X0 X1)
               have i₂ := b8e30 X0 X1
               grind)
            | exact superpose b8e30 b8e308
            | (have j0 := b8e308 (M.op X0 X1)
               grind)
            | exact resolve b8e308 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e826 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e308 (τ X0)
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e308
            | (have j0 := b8e308 (τ X0)
               grind)
            | exact resolve b8e308 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e829 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b8e821 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e821
          have b8e831 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e826 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e826
            | (have j0 := b8e826 X0
               grind)
            | exact resolve b8e826 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e826
          have b8e835 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e831 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e831
            | (have j0 := b8e831 X0
               grind)
            | exact resolve b8e831 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e846 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e835 (τ X0)
               have i₂ := b8e116 X0 X0
               grind)
            | exact superpose b8e116 b8e835
            | (have j0 := b8e835 (τ X0)
               grind)
            | exact resolve b8e835 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1431 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = (M.op (σ (M.op (τ X0) (τ X0))) X1) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e106 X0
               have i₂ := b8e73 (σ (M.op (τ X0) (τ X0))) X0 X1
               grind)
            | exact superpose b8e73 b8e106
            | (have j1 := b8e73 X0 (σ (M.op (τ X0) (τ X0))) X1
               grind)
            | exact resolve b8e106 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e1456 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e1460 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X1) = (M.op (σ (M.op (τ X0) (τ X0))) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e1431 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1431
          have b8e1599 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) ∨ (M.op (σ x) X0) = (k X0 (σ x)) ∨ (M.op (σ x) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e75 (σ x) (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e75 X0 (σ y) (σ x)
               grind)
            | exact superpose b8e75 b8e24
            | (have j1 := b8e75 (σ x) x X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e75 (σ y) x (σ x)
               grind)
            | exact resolve b8e24 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e2275 : (σ (M.op y x)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b8e526 (σ (M.op y x))
               have i₂ := b8e829 y x
               grind)
            | exact superpose b8e829 b8e526
            | exact resolve b8e526 b8e829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2300 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b8e2275
               have i₂ := b8e635 (σ y)
               grind)
            | exact superpose b8e635 b8e2275
            | exact resolve b8e2275 b8e635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e635 b8e2275
          have b8e2364 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            grind
          have b8e2378 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e307 (τ X1) (τ X0)
               have i₂ := b8e116 X1 X0
               grind)
            | exact superpose b8e116 b8e307
            | (have j0 := b8e307 (τ X1) (τ X0)
               grind)
            | exact resolve b8e307 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e307
          have b8e2400 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have j0 := b8e2364 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2364
          have b8e2407 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2378 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e2378
            | (have j0 := b8e2378 X0 X1
               grind)
            | exact resolve b8e2378 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2378
          have b8e2417 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2407 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e2407
            | (have j0 := b8e2407 X0 X1
               grind)
            | exact resolve b8e2407 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2407
          have b8e2421 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2417 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e2417
            | (have j0 := b8e2417 X0 X1
               grind)
            | exact resolve b8e2417 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2417
          have b8e2422 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2421 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e2421
            | (have j0 := b8e2421 X0 X1
               grind)
            | exact resolve b8e2421 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2421
          have b8e2423 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e2422 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e2422
            | (have j0 := b8e2422 X0 X1
               grind)
            | exact resolve b8e2422 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2422
          have b8e2424 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e2423 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e2423
            | (have j0 := b8e2423 X0 X1
               grind)
            | exact resolve b8e2423 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2423
          have b8e6952 : ∀ X0 X1 : G, (τ (M.op X0 X1)) ≠ (τ (M.op X0 X1)) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e846 (M.op X0 X1)
               have i₂ := b8e30 X0 X1
               grind)
            | exact superpose b8e30 b8e846
            | (have j0 := b8e846 (M.op X0 X1)
               grind)
            | exact resolve b8e846 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e846
          have b8e6965 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have j0 := b8e6952 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6952
          have b8e7297 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e311 (τ X0) X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e311
            | (have j0 := b8e311 (τ X0) X1
               grind)
            | exact resolve b8e311 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e311
          have b8e7641 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e7297 X0 X1
               have j1 := b8e1456 X1 X0
               grind)
            | (have r₁ := b8e7297 X1 X1
               have r₂ := b8e1456 X0 X1
               grind)
            | (have r₁ := b8e7297 X0 (M.op (σ (k (τ X0) (τ X0))) (σ (k (τ X0) (τ X0))))
               have r₂ := b8e1456 X0 (σ (k (τ X0) (τ X0)))
               grind)
            | (have r₁ := b8e7297 X1 X1
               have r₂ := b8e1456 X0 X1
               grind)
            | exact resolve b8e7297 b8e1456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7297
          have b8e7696 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e7641 X0 X1
               have i₂ := b8e27 X0 (τ X0)
               grind)
            | exact superpose b8e27 b8e7641
            | (have j0 := b8e7641 X0 X1
               grind)
            | exact resolve b8e7641 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e7641
          have b8e7732 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e7696 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e7696
            | (have j0 := b8e7696 X0 X1
               grind)
            | exact resolve b8e7696 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7696
          have b8e20815 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1456 X1 (σ X0)
               have i₂ := b8e71 X0 X0
               grind)
            | exact superpose b8e71 b8e1456
            | (have j0 := b8e1456 X1 (σ X0)
               have j1 := b8e71 X0 X0
               grind)
            | (have r₁ := b8e1456 X0 (σ X0)
               have r₂ := b8e71 X0 X0
               grind)
            | (have r₁ := b8e1456 X0 (σ X1)
               have r₂ := b8e71 X1 X1
               grind)
            | exact resolve b8e1456 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e20840 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e20815 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20815
          have b8e20850 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e20840 X0 X1
               have j1 := b8e1456 X1 (σ X0)
               grind)
            | (have r₁ := b8e20840 X0 (σ X0)
               have r₂ := b8e1456 X0 (σ X0)
               grind)
            | (have r₁ := b8e20840 X0 X1
               have r₂ := b8e1456 X0 (σ X0)
               grind)
            | exact resolve b8e20840 b8e1456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20840
          have b8e24771 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e2424 X1 X1
               have i₂ := b8e7732 X1 X0
               grind)
            | (have i₁ := b8e2424 X0 X1
               have i₂ := b8e7732 X0 (k X0 X1)
               grind)
            | exact superpose b8e7732 b8e2424
            | (have j0 := b8e2424 X1 X1
               have j1 := b8e7732 X1 X0
               grind)
            | (have r₁ := b8e2424 X1 X1
               have r₂ := b8e7732 X1 X1
               grind)
            | (have r₁ := b8e2424 (k X0 X0) X1
               have r₂ := b8e7732 X0 (k (k X0 X0) X1)
               grind)
            | exact resolve b8e2424 b8e7732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2424
          have b8e24814 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e24771 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24771
          have b8e24880 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e24814 X0 X1
               have j1 := b8e1456 X0 X1
               grind)
            | (have r₁ := b8e24814 (M.op X0 X1) (k X1 X0)
               have r₂ := b8e1456 X0 X1
               grind)
            | (have r₁ := b8e24814 (k X1 X0) (M.op X0 X1)
               have r₂ := b8e1456 X0 X1
               grind)
            | (have r₁ := b8e24814 (M.op X0 X1) X1
               have r₂ := b8e1456 X0 X1
               grind)
            | exact resolve b8e24814 b8e1456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1456 b8e24814
          have b8e32009 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e30 (σ (M.op (τ X0) (τ X0))) X0
               have i₂ := b8e142 X0
               grind)
            | exact superpose b8e142 b8e30
            | (have j1 := b8e142 X0
               grind)
            | exact resolve b8e30 b8e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142
          have b8e32174 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e32009 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e32009
            | (have j0 := b8e32009 (σ X0)
               grind)
            | exact resolve b8e32009 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32226 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e32009 X0
               grind)
            | exact superpose b8e32009 b8e14
            | (have j1 := b8e32009 X0
               grind)
            | exact resolve b8e14 b8e32009
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32009
          have b8e32433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e32174 X0
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e32174
            | (have j0 := b8e32174 X0
               grind)
            | exact resolve b8e32174 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32174
          have b8e33156 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e32226 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e32226
            | (have j0 := b8e32226 (σ X0)
               grind)
            | exact resolve b8e32226 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33265 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e33156 X0
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e33156
            | (have j0 := b8e33156 X0
               grind)
            | exact resolve b8e33156 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33156
          have b8e35870 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e18 (σ X0) X1
               have i₂ := b8e32433 X0
               grind)
            | exact superpose b8e32433 b8e18
            | (have j0 := b8e18 (σ X0) X1
               have j1 := b8e32433 X0
               grind)
            | exact resolve b8e18 b8e32433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35943 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e35870 X0 X1
               have j1 := b8e20850 X0 X1
               grind)
            | (have r₁ := b8e35870 X0 (σ (k (M.op X0 X0) (M.op X0 X0)))
               have r₂ := b8e20850 (M.op X0 X0) X1
               grind)
            | (have r₁ := b8e35870 X0 X1
               have r₂ := b8e20850 X0 X1
               grind)
            | exact resolve b8e35870 b8e20850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35870
          have b8e38282 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e33265 X0
               have i₂ := b8e316 X0 X0
               grind)
            | exact superpose b8e316 b8e33265
            | (have j0 := b8e33265 X0
               have j1 := b8e316 X0 X0
               grind)
            | exact resolve b8e33265 b8e316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e316 b8e33265
          have b8e38364 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e38282 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38282
          have b8e38398 : ∀ X0 : G, (M.op X0 X0) = (τ (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b8e38364 X0
               have j1 := b8e308 X0
               grind)
            | (have r₁ := b8e38364 X0
               have r₂ := b8e308 X0
               grind)
            | exact resolve b8e38364 b8e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e308 b8e38364
          have b8e38468 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e38398 X0
               have i₂ := b8e14 (k X0 X0)
               grind)
            | exact superpose b8e14 b8e38398
            | (have j0 := b8e38398 X0
               grind)
            | exact resolve b8e38398 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38398
          have b8e39973 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e38468 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e38468
            | (have j0 := b8e38468 (τ X0)
               grind)
            | exact resolve b8e38468 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40069 : ∀ X0 : G, (k X0 (τ (τ (σ (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e443 X0
               have i₂ := b8e38468 (σ X0)
               grind)
            | exact superpose b8e38468 b8e443
            | (have j1 := b8e38468 (σ X0)
               grind)
            | exact resolve b8e443 b8e38468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e443
          have b8e40097 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e30 (σ X0) (σ X0)
               have i₂ := b8e38468 X0
               grind)
            | exact superpose b8e38468 b8e30
            | (have j1 := b8e38468 X0
               grind)
            | exact resolve b8e30 b8e38468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38468
          have b8e40136 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b8e40097 X0
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e40097
            | (have j0 := b8e40097 X0
               grind)
            | exact resolve b8e40097 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40097
          have b8e40146 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e40069 X0
               have i₂ := b8e14 (σ X0)
               grind)
            | exact superpose b8e14 b8e40069
            | (have j0 := b8e40069 X0
               grind)
            | exact resolve b8e40069 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40069
          have b8e40164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e39973 X0
               have i₂ := b8e116 X0 X0
               grind)
            | exact superpose b8e116 b8e39973
            | (have j0 := b8e39973 X0
               grind)
            | exact resolve b8e39973 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39973
          have b8e40168 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e40146 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e40146
            | (have j0 := b8e40146 X0
               grind)
            | exact resolve b8e40146 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40146
          have b8e40172 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e40168 X0
               have i₂ := b8e19 X0 X0
               grind)
            | exact superpose b8e19 b8e40168
            | (have j0 := b8e40168 X0
               grind)
            | exact resolve b8e40168 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40168
          have b8e42871 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e40136 (τ X0)
               grind)
            | exact superpose b8e40136 b8e26
            | (have j1 := b8e40136 (τ X0)
               grind)
            | exact resolve b8e26 b8e40136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e40136
          have b8e43037 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e42871 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e42871
            | (have j0 := b8e42871 X0
               grind)
            | exact resolve b8e42871 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42871
          have b8e43078 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e43037 X0
               have i₂ := b8e116 X0 X0
               grind)
            | exact superpose b8e116 b8e43037
            | (have j0 := b8e43037 X0
               grind)
            | exact resolve b8e43037 b8e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116 b8e43037
          have b8e45713 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e40164 X0
               have i₂ := b8e32226 X0
               grind)
            | exact superpose b8e32226 b8e40164
            | (have j0 := b8e40164 X0
               have j1 := b8e32226 X0
               grind)
            | exact resolve b8e40164 b8e32226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32226
          have b8e45766 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (k X0 X0)) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e32 (τ X0) (τ X0) X1
               have i₂ := b8e40164 X0
               grind)
            | exact superpose b8e40164 b8e32
            | (have j1 := b8e40164 X0
               grind)
            | exact resolve b8e32 b8e40164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40164
          have b8e45835 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e45713 X0
               have j1 := b8e835 X0
               grind)
            | (have r₁ := b8e45713 X0
               have r₂ := b8e835 X0
               grind)
            | exact resolve b8e45713 b8e835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e835 b8e45713
          have b8e46074 : ∀ X0 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e6965 (σ (M.op X0 X0)) (σ X0)
               have i₂ := b8e2400 X0
               grind)
            | exact superpose b8e2400 b8e6965
            | (have j1 := b8e2400 X0
               grind)
            | exact resolve b8e6965 b8e2400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2400
          have b8e46107 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e46074 X0
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e46074
            | (have j0 := b8e46074 X0
               grind)
            | exact resolve b8e46074 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46074
          have b8e47505 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e32 (σ X0) (σ X0) X1
               have i₂ := b8e46107 X0
               grind)
            | exact superpose b8e46107 b8e32
            | (have j1 := b8e46107 X0
               grind)
            | exact resolve b8e32 b8e46107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46107
          have b8e48326 : ∀ X0 : G, (τ (σ (k X0 X0))) = (M.op (τ (σ (k X0 X0))) (τ (σ (k X0 X0)))) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e6965 (σ X0) (σ X0)
               have i₂ := b8e40172 X0
               grind)
            | exact superpose b8e40172 b8e6965
            | (have j1 := b8e40172 X0
               grind)
            | exact resolve b8e6965 b8e40172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40172
          have b8e48335 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e48326 X0
               have i₂ := b8e14 (k X0 X0)
               grind)
            | exact superpose b8e14 b8e48326
            | (have j0 := b8e48326 X0
               grind)
            | exact resolve b8e48326 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48326
          have b8e61513 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (M.op (τ X0) (τ X0))) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ (M.op (τ X0) (τ X0))) X0
               have i₂ := b8e1460 X0 X1
               grind)
            | exact superpose b8e1460 b8e30
            | (have j1 := b8e1460 X0 X1
               grind)
            | exact resolve b8e30 b8e1460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e1460
          have b8e62448 : (σ x) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b8e1599 (σ y)
               have i₂ := b8e32433 y
               grind)
            | exact superpose b8e32433 b8e1599
            | (have j0 := b8e1599 (σ y)
               have j1 := b8e32433 y
               grind)
            | exact resolve b8e1599 b8e32433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1599 b8e32433
          have b8e62502 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) := by
            first
            | (have j1 := b8e35943 y (σ x)
               grind)
            | (have r₁ := b8e62448
               have r₂ := b8e35943 y (σ x)
               grind)
            | exact resolve b8e62448 b8e35943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35943 b8e62448
          have b8e62516 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j1 := b8e20850 y (σ x)
               grind)
            | (have r₁ := b8e62502
               have r₂ := b8e20850 y x
               grind)
            | exact resolve b8e62502 b8e20850
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20850 b8e62502
          have b8e62524 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e62516
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e62516
            | exact resolve b8e62516 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62516
          have b8e64495 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e45766 X0 X1
               have i₂ := b8e45835 X0
               grind)
            | exact superpose b8e45835 b8e45766
            | (have j0 := b8e45766 X0 X1
               have j1 := b8e45835 X0
               grind)
            | exact resolve b8e45766 b8e45835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45766 b8e45835
          have b8e64637 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 X0)) X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e64495 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64495
          have b8e126932 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (τ (k X0 X0))) X1) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e61513 X0 X1
               have i₂ := b8e43078 X0
               grind)
            | exact superpose b8e43078 b8e61513
            | (have j0 := b8e61513 X0 X1
               have j1 := b8e43078 X0
               grind)
            | exact resolve b8e61513 b8e43078
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43078 b8e61513
          have b8e127329 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (τ (k X0 X0))) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e126932 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126932
          have b8e127417 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (k X0 X0) X1) ∨ (k X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e127329 X0 X1
               have i₂ := b8e15 (k X0 X0)
               grind)
            | exact superpose b8e15 b8e127329
            | (have j0 := b8e127329 X0 X1
               grind)
            | exact resolve b8e127329 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127329
          have b8e128604 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e48335 X0
               have i₂ := b8e127417 X0 (k X0 X0)
               grind)
            | exact superpose b8e127417 b8e48335
            | (have j0 := b8e48335 X0
               have j1 := b8e127417 X0 x
               grind)
            | exact resolve b8e48335 b8e127417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48335 b8e127417
          have b8e128611 : ∀ X0 : G, (k X0 X0) = (M.op X0 (k X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b8e128604 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128604
          have b8e129636 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e128611 X0
               have i₂ := b8e7732 X0 X1
               grind)
            | (have i₁ := b8e128611 X0
               have i₂ := b8e7732 X0 (k X0 X0)
               grind)
            | exact superpose b8e7732 b8e128611
            | (have j1 := b8e7732 X1 X0
               grind)
            | exact resolve b8e128611 b8e7732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7732 b8e128611
          have b8e129909 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e129636 X0 X1
               have j1 := b8e24880 X0 X1
               grind)
            | (have r₁ := b8e129636 X1 X1
               have r₂ := b8e24880 (M.op X1 X1) X1
               grind)
            | (have r₁ := b8e129636 X0 X1
               have r₂ := b8e24880 X0 (M.op X1 X0)
               grind)
            | (have r₁ := b8e129636 X0 X1
               have r₂ := b8e24880 X0 X1
               grind)
            | exact resolve b8e129636 b8e24880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24880 b8e129636
          have b8e374851 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62524
               grind)
            | exact superpose b8e62524 b8e20
            | exact resolve b8e20 b8e62524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62524
          have b8e376628 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e374851
               have i₂ := b8e129909 x y
               grind)
            | exact superpose b8e129909 b8e374851
            | (have j1 := b8e129909 x y
               grind)
            | exact resolve b8e374851 b8e129909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129909 b8e374851
          have b8e376635 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e376628
          have b8e376643 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e376635
               have r₂ := b8e22
               grind)
            | exact resolve b8e376635 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e376635
          have b8e377613 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e32 (σ x) (σ y) X0
               have i₂ := b8e376643
               grind)
            | exact superpose b8e376643 b8e32
            | exact resolve b8e32 b8e376643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e377631 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e6965 (σ x) (σ y)
               have i₂ := b8e376643
               grind)
            | exact superpose b8e376643 b8e6965
            | exact resolve b8e6965 b8e376643
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6965 b8e376643
          have b8e377663 : y = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e377631
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e377631
            | exact resolve b8e377631 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e377631
          have b8e396145 : (M.op (σ x) (σ x)) = (σ (M.op y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e2300
               have i₂ := b8e377613 (σ x)
               grind)
            | exact superpose b8e377613 b8e2300
            | exact resolve b8e2300 b8e377613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2300 b8e377613
          have b8e424044 : ∀ X0 : G, (M.op (τ (σ (M.op y x))) X0) = (M.op (τ (σ x)) X0) ∨ (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e64637 (σ x) x
               have i₂ := b8e396145
               grind)
            | exact superpose b8e396145 b8e64637
            | exact resolve b8e64637 b8e396145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64637 b8e396145
          have b8e424159 : ∀ X0 : G, (M.op (τ (σ (M.op y x))) X0) = (M.op (τ (σ x)) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b8e424044 X0
               grind)
            | (have r₁ := b8e424044 X0
               have r₂ := b8e227
               grind)
            | exact resolve b8e424044 b8e227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e227 b8e424044
          have b8e424254 : ∀ X0 : G, (M.op x X0) = (M.op (τ (σ (M.op y x))) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e424159 X0
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e424159
            | exact resolve b8e424159 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e424159
          have b8e424287 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y x) X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e424254 X0
               have i₂ := b8e14 (M.op y x)
               grind)
            | exact superpose b8e14 b8e424254
            | exact resolve b8e424254 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e424254
          have b8e424301 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e424287 X0
               have i₂ := b8e32 y x X0
               grind)
            | exact superpose b8e32 b8e424287
            | exact resolve b8e424287 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e424287
          have b8e430318 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e377663
               have i₂ := b8e424301 y
               grind)
            | exact superpose b8e424301 b8e377663
            | exact resolve b8e377663 b8e424301
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e377663 b8e424301
          have b8e430319 : y = (M.op x y) := by grind
          clear b8e430318
          have b8e432382 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b8e32 x y X0
               have i₂ := b8e430319
               grind)
            | exact superpose b8e430319 b8e32
            | exact resolve b8e32 b8e430319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e432397 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e829 x y
               have i₂ := b8e430319
               grind)
            | exact superpose b8e430319 b8e829
            | exact resolve b8e829 b8e430319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e829
          have b8e435772 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e432382 x
               grind)
            | exact superpose b8e432382 b8e22
            | exact resolve b8e22 b8e432382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e435776 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b8e526 X0
               have i₂ := b8e432382 x
               grind)
            | exact superpose b8e432382 b8e526
            | exact resolve b8e526 b8e432382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526 b8e432382
          have b8e462065 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e47505 x X0
               have i₂ := b8e435776 X0
               grind)
            | exact superpose b8e435776 b8e47505
            | (have j0 := b8e47505 x x
               grind)
            | exact resolve b8e47505 b8e435776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47505 b8e435776
          have b8e462210 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e462065 X0
               grind)
            | (have r₁ := b8e462065 X0
               have r₂ := b8e435772
               grind)
            | exact resolve b8e462065 b8e435772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e435772 b8e462065
          have b8e467249 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e432397
               have i₂ := b8e462210 (σ y)
               grind)
            | exact superpose b8e462210 b8e432397
            | exact resolve b8e432397 b8e462210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e432397 b8e462210
          have b8e470127 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e467249
               grind)
            | exact superpose b8e467249 b8e20
            | exact resolve b8e20 b8e467249
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e467249
          have b8e470226 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e470127
               have i₂ := b8e430319
               grind)
            | exact superpose b8e430319 b8e470127
            | exact resolve b8e470127 b8e430319
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e430319 b8e470127
          have b8e470227 : False := by grind
          exact b8e470227
