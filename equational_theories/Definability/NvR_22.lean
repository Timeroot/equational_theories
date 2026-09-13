import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e73 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e78 : False := by grind
      exact b0e78
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e80 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 (M.op X1 X0) (M.op X0 X0)
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e89 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e80
          have b4e90 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e89 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89
          have b4e93 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e77 X0 X1
               have i₂ := b4e30 X1
               grind)
            | exact superpose b4e30 b4e77
            | (have j0 := b4e77 X0 X1
               grind)
            | exact resolve b4e77 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e77
          have b4e257 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e260 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e257 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e257 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e257 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e257 X0 X1
               have r₂ := b4e18 (M.op X1 X0) (M.op X0 X0)
               grind)
            | exact resolve b4e257 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257
          have b4e281 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 X1
               have i₂ := b4e260 X1 (τ X0)
               grind)
            | exact superpose b4e260 b4e27
            | (have j1 := b4e260 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b4e27 b4e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e283 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e49 X1 X0
               have i₂ := b4e260 (σ X1) X0
               grind)
            | exact superpose b4e260 b4e49
            | (have j1 := b4e260 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
               grind)
            | exact resolve b4e49 b4e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e260
          have b4e641 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e93 x y
               grind)
            | exact superpose b4e93 b4e20
            | (have j1 := b4e93 x y
               grind)
            | exact resolve b4e20 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e694 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e641
               have r₂ := b4e23
               grind)
            | exact resolve b4e641 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e641
          have b4e2365 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e281 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e281
            | exact resolve b4e281 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e281
          have b4e2412 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e2365 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e2365
            | (have j0 := b4e2365 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b4e2365 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2365
          have b4e7629 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b4e694
               have i₂ := b4e2412 x y
               grind)
            | exact superpose b4e2412 b4e694
            | (have j1 := b4e2412 (M.op (σ x) (σ y)) (σ (M.op y y))
               grind)
            | (have r₁ := b4e694
               have r₂ := b4e2412 x y
               grind)
            | (have r₁ := b4e694
               have r₂ := b4e2412 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e694
               have r₂ := b4e2412 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e694 b4e2412
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e694
          have b4e7630 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by grind
          clear b4e7629
          have b4e7635 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e7630
               have r₂ := b4e21
               grind)
            | exact resolve b4e7630 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7630
          have b4e7641 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e7635
               grind)
            | exact superpose b4e7635 b4e20
            | exact resolve b4e20 b4e7635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7650 : (τ (σ (M.op y y))) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e283 (σ x) y
               have i₂ := b4e7635
               grind)
            | exact superpose b4e7635 b4e283
            | (have j0 := b4e283 (σ y) x
               grind)
            | exact resolve b4e283 b4e7635
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e283 b4e7635
          have b4e7696 : (τ (σ (M.op y y))) = (k y (τ (σ x))) := by
            first
            | (have r₁ := b4e7650
               have r₂ := b4e23
               grind)
            | exact resolve b4e7650 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7650
          have b4e7701 : (k y x) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b4e7696
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e7696
            | exact resolve b4e7696 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7696
          have b4e7703 : (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e7701
               have i₂ := b4e14 (M.op y y)
               grind)
            | exact superpose b4e14 b4e7701
            | exact resolve b4e7701 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7701
          have b4e7799 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b4e2412 x y
               have i₂ := b4e7703
               grind)
            | exact superpose b4e7703 b4e2412
            | (have j0 := b4e2412 (σ (M.op x y)) (σ (M.op y y))
               grind)
            | exact resolve b4e2412 b4e7703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2412 b4e7703
          have b4e7802 : x = y := by
            first
            | (have r₁ := b4e7799
               have r₂ := b4e7641
               grind)
            | exact resolve b4e7799 b4e7641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7641 b4e7799
          have b4e7808 : False := by grind
          exact b4e7808
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op x x) = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e59 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k x y) := by
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
          have b5e62 : x = y ∨ (M.op x x) = (k x y) := by grind
          clear b5e59
          have b5e63 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e69 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e69 X0 X1
               have i₂ := b5e30 X1
               grind)
            | exact superpose b5e30 b5e69
            | (have j0 := b5e69 X0 X1
               grind)
            | exact resolve b5e69 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e561 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e85 y x
               grind)
            | exact superpose b5e85 b5e24
            | (have j1 := b5e85 y x
               grind)
            | exact resolve b5e24 b5e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e610 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e561
               have r₂ := b5e23
               grind)
            | exact resolve b5e561 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e561
          have b5e624 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e610
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e610
            | exact resolve b5e610 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e610
          have b5e630 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e624
               have r₂ := b5e30 x
               grind)
            | exact resolve b5e624 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e624
          have b5e633 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e630
               grind)
            | exact superpose b5e630 b5e24
            | exact resolve b5e24 b5e630
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e630
          have b5e650 : False := by grind
          exact b5e650
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e63 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e60
          have b7e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e23
               grind)
            | exact resolve b7e63 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e65 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e64
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e64
            | exact resolve b7e64 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e66 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e65
            | exact resolve b7e65 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e65
          have b7e70 : (k x y) = (τ (σ (M.op x x))) := by
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
          have b7e71 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e98 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (M.op y x) ∨ x = y := by
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
          have b7e99 : (M.op x x) = (M.op y x) ∨ x = y := by grind
          clear b7e98
          have b7e101 : x = y := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e22
               grind)
            | exact resolve b7e99 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e103 : False := by grind
          exact b7e103
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e47 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e76 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X0 X0)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e88 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e87 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87
          have b8e89 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e76 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e76
            | (have j0 := b8e76 X0 X1
               grind)
            | exact resolve b8e76 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e76
          have b8e192 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e195 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e192 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e192 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e192 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e192 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X0 X0)
               grind)
            | exact resolve b8e192 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e209 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e195 X1 (τ X0)
               grind)
            | exact superpose b8e195 b8e27
            | (have j1 := b8e195 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e211 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e47 X1 X0
               have i₂ := b8e195 (σ X1) X0
               grind)
            | exact superpose b8e195 b8e47
            | (have j1 := b8e195 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
               grind)
            | exact resolve b8e47 b8e195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47 b8e195
          have b8e521 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e89 x y
               grind)
            | exact superpose b8e89 b8e20
            | (have j1 := b8e89 x y
               grind)
            | exact resolve b8e20 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e572 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e521
               have r₂ := b8e23
               grind)
            | exact resolve b8e521 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e521
          have b8e1832 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e209 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e209
            | exact resolve b8e209 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209
          have b8e1875 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e1832 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e1832
            | (have j0 := b8e1832 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e1832 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1832
          have b8e5998 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b8e572
               have i₂ := b8e1875 x y
               grind)
            | exact superpose b8e1875 b8e572
            | (have j1 := b8e1875 (M.op (σ x) (σ y)) (σ (M.op y y))
               grind)
            | (have r₁ := b8e572
               have r₂ := b8e1875 x y
               grind)
            | (have r₁ := b8e572
               have r₂ := b8e1875 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e572
               have r₂ := b8e1875 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e572 b8e1875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e572
          have b8e5999 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y := by grind
          clear b8e5998
          have b8e6004 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e5999
               have r₂ := b8e21
               grind)
            | exact resolve b8e5999 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5999
          have b8e6010 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6004
               grind)
            | exact superpose b8e6004 b8e20
            | exact resolve b8e20 b8e6004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6019 : (τ (σ (M.op y y))) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e211 (σ x) y
               have i₂ := b8e6004
               grind)
            | exact superpose b8e6004 b8e211
            | (have j0 := b8e211 (σ y) x
               grind)
            | exact resolve b8e211 b8e6004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211 b8e6004
          have b8e6061 : (τ (σ (M.op y y))) = (k y (τ (σ x))) := by
            first
            | (have r₁ := b8e6019
               have r₂ := b8e23
               grind)
            | exact resolve b8e6019 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6019
          have b8e6067 : (k y x) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b8e6061
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e6061
            | exact resolve b8e6061 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6061
          have b8e6069 : (k y x) = (M.op y y) := by
            first
            | (have i₁ := b8e6067
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e6067
            | exact resolve b8e6067 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6067
          have b8e6091 : (σ (M.op x y)) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have i₁ := b8e1875 x y
               have i₂ := b8e6069
               grind)
            | exact superpose b8e6069 b8e1875
            | (have j0 := b8e1875 (σ (M.op x y)) (σ (M.op y y))
               grind)
            | exact resolve b8e1875 b8e6069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1875 b8e6069
          have b8e6094 : x = y := by
            first
            | (have r₁ := b8e6091
               have r₂ := b8e6010
               grind)
            | exact resolve b8e6091 b8e6010
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6010 b8e6091
          have b8e6100 : False := by grind
          exact b8e6100

/-- `Equation964`: `x = y ◇ ((z ◇ y) ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation964 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law964 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law964.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
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
          have b4e32 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
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
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
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
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X1 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X1) (M.op X1 X0)) X1 X2
               have i₂ := b4e13 X0 X1 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e32 (M.op y (M.op x X0))
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 x) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op (M.op X1 x) (M.op x X0))
               have i₂ := b4e13 X0 x X1
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e99 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e33 (M.op (σ y) (M.op (σ x) X0))
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e33
            | exact resolve b4e33 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e102 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) X0)) = (M.op (σ x) (M.op (M.op X1 (σ x)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op (σ y) (M.op (σ x) X0)) (σ x) X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e155 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ x)) X0) = (M.op (σ x) (M.op (M.op X2 (σ x)) (M.op (σ y) (M.op (σ x) X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e37 (M.op (σ y) (M.op (σ x) X0)) (σ x) X2 X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e37
            | exact resolve b4e37 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e193 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (M.op (σ y) (M.op (σ x) X0)))) = (M.op (M.op X1 (σ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e155 X0 X1 x
               have i₂ := b4e102 (M.op (σ y) (M.op (σ x) X0)) x
               grind)
            | exact superpose b4e102 b4e155
            | exact resolve b4e155 b4e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102 b4e155
          have b4e197 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e193 X0 X1
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e193
            | exact resolve b4e193 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e193
          have b4e346 : (M.op x y) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b4e38 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e38
            | exact resolve b4e38 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e561 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b4e197 X0 (σ x)
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e197
            | exact resolve b4e197 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197
          have b4e823 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
            first
            | (have i₁ := b4e30 (M.op x x)
               have i₂ := b4e561 (σ (M.op x x))
               grind)
            | exact superpose b4e561 b4e30
            | exact resolve b4e30 b4e561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e561
          have b4e858 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op y x))) := by
            first
            | (have i₁ := b4e823
               have i₂ := b4e39 x x
               grind)
            | exact superpose b4e39 b4e823
            | exact resolve b4e823 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e823
          have b4e864 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b4e858
               have i₂ := b4e38 x
               grind)
            | exact superpose b4e38 b4e858
            | exact resolve b4e858 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e858
          have b4e866 : (σ (M.op x y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e864
               have i₂ := b4e346
               grind)
            | exact superpose b4e346 b4e864
            | exact resolve b4e864 b4e346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e346 b4e864
          have b4e2284 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b4e99 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e99
            | exact resolve b4e99 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99
          have b4e2336 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b4e2284
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e2284
            | exact resolve b4e2284 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e2284
          have b4e2348 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e2336
               have i₂ := b4e866
               grind)
            | exact superpose b4e866 b4e2336
            | exact resolve b4e2336 b4e866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e866 b4e2336
          have b4e2356 : False := by grind
          exact b4e2356
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e34 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) := by
            intro X0
            first
            | (have i₁ := b5e13 x y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e231 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e47 x y
               grind)
            | exact superpose b5e47 b5e20
            | (have j1 := b5e47 x y
               grind)
            | exact resolve b5e20 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e242 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e231
               have r₂ := b5e23
               grind)
            | exact resolve b5e231 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231
          have b5e4022 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e242
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e242
            | (have j1 := b5e18 y x
               grind)
            | (have r₁ := b5e242
               have r₂ := b5e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b5e242
               have r₂ := b5e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b5e242 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e242
          have b5e4023 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e4022
          have b5e4024 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e4023
               have r₂ := b5e21
               grind)
            | exact resolve b5e4023 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4023
          have b5e4191 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e4024
               grind)
            | exact superpose b5e4024 b5e20
            | exact resolve b5e20 b5e4024
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4196 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e4024
               grind)
            | exact superpose b5e4024 b5e17
            | (have j0 := b5e17 (σ x) (σ y)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e4024
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e4024
               grind)
            | exact resolve b5e17 b5e4024
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4024
          have b5e4214 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b5e4196
          have b5e4227 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e4214
               have r₂ := b5e23
               grind)
            | exact resolve b5e4214 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4214
          have b5e4231 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e4227
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e4227
            | exact resolve b5e4227 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4227
          have b5e4592 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e4231
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e4231
            | (have j1 := b5e18 y x
               grind)
            | exact resolve b5e4231 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4231
          have b5e4614 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e4592
          have b5e4632 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b5e4614
               have r₂ := b5e4191
               grind)
            | exact resolve b5e4614 b5e4191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4191 b5e4614
          have b5e4633 : x = (M.op x y) := by
            first
            | (have r₁ := b5e4632
               have r₂ := b5e21
               grind)
            | exact resolve b5e4632 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4632
          have b5e5211 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e4633
               grind)
            | exact superpose b5e4633 b5e34
            | exact resolve b5e34 b5e4633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e5264 : x = (M.op y x) := by
            first
            | (have i₁ := b5e5211
               have i₂ := b5e4633
               grind)
            | exact superpose b5e4633 b5e5211
            | exact resolve b5e5211 b5e4633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4633 b5e5211
          have b5e5282 : x = y := by
            first
            | (have i₁ := b5e5264
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e5264
            | exact resolve b5e5264 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5264
          have b5e5290 : False := by grind
          exact b5e5290
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
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e46 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ y) = (σ (k x y)) := by
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
          have b7e50 : (k x y) = (τ (σ y)) := by
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
          have b7e51 : y = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : y = (M.op y x) ∨ x = y := by grind
          clear b7e61
          have b7e64 : x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : False := by grind
          exact b7e66
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e169 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e180 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e169
               have r₂ := b8e23
               grind)
            | exact resolve b8e169 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e169
          have b8e2150 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e180
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e180
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e180
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e180
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e180 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2151 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e2150
          have b8e2152 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e2151
               have r₂ := b8e21
               grind)
            | exact resolve b8e2151 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2151
          have b8e2154 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2152
               grind)
            | exact superpose b8e2152 b8e20
            | exact resolve b8e20 b8e2152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2161 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e2152
               grind)
            | exact superpose b8e2152 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e2152
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e2152
               grind)
            | exact resolve b8e17 b8e2152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2152
          have b8e2180 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e2161
          have b8e2194 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e2180
               have r₂ := b8e23
               grind)
            | exact resolve b8e2180 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2180
          have b8e2203 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e2194
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e2194
            | exact resolve b8e2194 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2194
          have b8e2691 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e2203
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e2203
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e2203 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2203
          have b8e2717 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e2691
          have b8e2736 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e2717
               have r₂ := b8e2154
               grind)
            | exact resolve b8e2717 b8e2154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2154 b8e2717
          have b8e2737 : x = (M.op x y) := by
            first
            | (have r₁ := b8e2736
               have r₂ := b8e21
               grind)
            | exact resolve b8e2736 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2736
          have b8e3100 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e2737
               grind)
            | exact superpose b8e2737 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e2737
               grind)
            | exact resolve b8e17 b8e2737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3120 : x = y ∨ x = (k y x) := by grind
          clear b8e3100
          have b8e3125 : x = (k y x) := by
            first
            | (have r₁ := b8e3120
               have r₂ := b8e21
               grind)
            | exact resolve b8e3120 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3120
          have b8e3889 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e180
               have i₂ := b8e3125
               grind)
            | exact superpose b8e3125 b8e180
            | exact resolve b8e180 b8e3125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180 b8e3125
          have b8e3893 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e3889
               have i₂ := b8e2737
               grind)
            | exact superpose b8e2737 b8e3889
            | exact resolve b8e3889 b8e2737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3889
          have b8e3894 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e3893
          have b8e3942 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3894
               grind)
            | exact superpose b8e3894 b8e20
            | exact resolve b8e20 b8e3894
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3894
          have b8e4004 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e3942
               have i₂ := b8e2737
               grind)
            | exact superpose b8e2737 b8e3942
            | exact resolve b8e3942 b8e2737
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2737 b8e3942
          have b8e4005 : False := by grind
          exact b8e4005
