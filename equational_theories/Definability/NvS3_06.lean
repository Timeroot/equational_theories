import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation883`: `x = y ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation883 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law883 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law883.models_iff G M).mp hM
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
      have b0e60 : False := by grind
      exact b0e60
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
          have b4e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e115 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 x y
               grind)
            | exact superpose b4e48 b4e20
            | (have j1 := b4e48 x y
               grind)
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e122 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e115
               have r₂ := b4e23
               grind)
            | exact resolve b4e115 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115
          have b4e441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e122
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e122
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e122
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e122
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e122 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e442 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e441
          have b4e443 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e442
               have r₂ := b4e21
               grind)
            | exact resolve b4e442 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e442
          have b4e445 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e443
               grind)
            | exact superpose b4e443 b4e20
            | exact resolve b4e20 b4e443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e448 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e443
               grind)
            | exact superpose b4e443 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e443
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e443
               grind)
            | exact resolve b4e17 b4e443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e443
          have b4e450 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e448
          have b4e452 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e450
               have r₂ := b4e23
               grind)
            | exact resolve b4e450 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e450
          have b4e455 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e452
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e452
            | exact resolve b4e452 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e452
          have b4e522 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e455
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e455
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e455 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e455
          have b4e543 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e522
          have b4e559 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e543
               have r₂ := b4e445
               grind)
            | exact resolve b4e543 b4e445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e445 b4e543
          have b4e560 : x = (M.op x y) := by
            first
            | (have r₁ := b4e559
               have r₂ := b4e21
               grind)
            | exact resolve b4e559 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e559
          have b4e601 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e560
               grind)
            | exact superpose b4e560 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e560
               grind)
            | exact resolve b4e17 b4e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e603 : x = y ∨ x = (k y x) := by grind
          clear b4e601
          have b4e604 : x = (k y x) := by
            first
            | (have r₁ := b4e603
               have r₂ := b4e21
               grind)
            | exact resolve b4e603 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e603
          have b4e660 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e122
               have i₂ := b4e604
               grind)
            | exact superpose b4e604 b4e122
            | exact resolve b4e122 b4e604
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e122 b4e604
          have b4e664 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e660
               have i₂ := b4e560
               grind)
            | exact superpose b4e560 b4e660
            | exact resolve b4e660 b4e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e660
          have b4e665 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e664
          have b4e695 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e665
               grind)
            | exact superpose b4e665 b4e20
            | exact resolve b4e20 b4e665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e665
          have b4e704 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e695
               have i₂ := b4e560
               grind)
            | exact superpose b4e560 b4e695
            | exact resolve b4e695 b4e560
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e560 b4e695
          have b4e705 : False := by grind
          exact b4e705
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
          have b5e35 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e38 : x = y ∨ y = (k x y) := by grind
          clear b5e35
          have b5e39 : y = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e21
               grind)
            | exact resolve b5e38 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e42 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e579 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e96 y x
               have i₂ := b5e39
               grind)
            | exact superpose b5e39 b5e96
            | (have j0 := b5e96 y x
               grind)
            | exact resolve b5e96 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e96
          have b5e586 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e579
          have b5e590 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e586
               have r₂ := b5e24
               grind)
            | exact resolve b5e586 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e586
          have b5e594 : False := by grind
          exact b5e594
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
          have b8e83 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e90 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e83
               have r₂ := b8e23
               grind)
            | exact resolve b8e83 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e356 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e90
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e90
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e90
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e90
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e90 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e357 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e356
          have b8e358 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e357
               have r₂ := b8e21
               grind)
            | exact resolve b8e357 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e357
          have b8e360 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e358
               grind)
            | exact superpose b8e358 b8e20
            | exact resolve b8e20 b8e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e363 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e358
               grind)
            | exact superpose b8e358 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e358
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e358
               grind)
            | exact resolve b8e17 b8e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e365 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e363
          have b8e367 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e365
               have r₂ := b8e23
               grind)
            | exact resolve b8e365 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e365
          have b8e370 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e367
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e367
            | exact resolve b8e367 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e367
          have b8e432 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e370
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e370
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e370 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e370
          have b8e452 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e432
          have b8e467 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e452
               have r₂ := b8e360
               grind)
            | exact resolve b8e452 b8e360
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e360 b8e452
          have b8e468 : x = (M.op x y) := by
            first
            | (have r₁ := b8e467
               have r₂ := b8e21
               grind)
            | exact resolve b8e467 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e467
          have b8e506 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e468
               grind)
            | exact resolve b8e17 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e508 : x = y ∨ x = (k y x) := by grind
          clear b8e506
          have b8e509 : x = (k y x) := by
            first
            | (have r₁ := b8e508
               have r₂ := b8e21
               grind)
            | exact resolve b8e508 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e508
          have b8e554 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e90
               have i₂ := b8e509
               grind)
            | exact superpose b8e509 b8e90
            | exact resolve b8e90 b8e509
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e509
          have b8e558 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e554
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e554
            | exact resolve b8e554 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e554
          have b8e559 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e558
          have b8e587 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e559
               grind)
            | exact superpose b8e559 b8e20
            | exact resolve b8e20 b8e559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e559
          have b8e596 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e587
               have i₂ := b8e468
               grind)
            | exact superpose b8e468 b8e587
            | exact resolve b8e587 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e468 b8e587
          have b8e597 : False := by grind
          exact b8e597

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation907 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law907 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
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
      have b0e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e17
        | exact resolve b0e17 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e52
        | exact resolve b0e52 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e52
      have b0e175 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e57 x
           grind)
        | exact superpose b0e57 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e57 x
           grind)
        | exact resolve b0e22 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e57
      have b0e184 : False := by grind
      exact b0e184
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e52 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e54 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e54
        have b1e58 : (k x y) = (M.op y y) := by grind
        clear b1e52
        have b1e59 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e57
          | exact resolve b1e57 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e60 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e56 y
             grind)
          | exact superpose b1e56 b1e59
          | exact resolve b1e59 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e56 (σ X0)
             grind)
          | exact superpose b1e56 b1e18
          | exact resolve b1e18 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e62 X0
             have i₂ := b1e56 X0
             grind)
          | exact superpose b1e56 b1e62
          | exact resolve b1e62 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e62
        have b1e75 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e77 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e75 X0
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e75
          | (have j0 := b1e75 X0
             grind)
          | exact resolve b1e75 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e133 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e23
          | exact resolve b1e23 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e774 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e77 (σ x)
             have i₂ := b1e60
             grind)
          | exact superpose b1e60 b1e77
          | (have j0 := b1e77 (σ x)
             grind)
          | (have r₁ := b1e77 (σ x)
             have r₂ := b1e60
             grind)
          | exact resolve b1e77 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60 b1e77
        have b1e775 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e774
        have b1e776 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e775
             have i₂ := b1e69 x
             grind)
          | exact superpose b1e69 b1e775
          | exact resolve b1e775 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775
        have b1e777 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e776
             have r₂ := b1e133
             grind)
          | exact resolve b1e776 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e776
        have b1e778 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e777
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e777
          | exact resolve b1e777 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e777
        have b1e779 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e778
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e778
          | exact resolve b1e778 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e778
        have b1e780 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e779
             have i₂ := b1e69 x
             grind)
          | exact superpose b1e69 b1e779
          | exact resolve b1e779 b1e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e69 b1e779
        have b1e781 : False := by grind
        exact b1e781
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : (k x y) = (M.op y y) := by grind
        clear b2e50
        have b2e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e18
          | exact resolve b2e18 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e55 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e55
          | exact resolve b2e55 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e55
        have b2e95 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
             have i₂ := b2e62 y
             grind)
          | exact superpose b2e62 b2e22
          | exact resolve b2e22 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e1406 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e95 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e1407 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1406
             have r₂ := b2e21
             grind)
          | exact resolve b2e1406 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1406
        have b2e1408 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1407
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1407
          | exact resolve b2e1407 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1407
        have b2e1409 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1408
             have i₂ := b2e53
             grind)
          | exact superpose b2e53 b2e1408
          | exact resolve b2e1408 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e1408
        have b2e1410 : False := by grind
        exact b2e1410
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b3e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e54
        have b3e59 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e57
          | exact resolve b3e57 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e56 (σ X0)
             grind)
          | exact superpose b3e56 b3e18
          | exact resolve b3e18 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e69 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e62 X0
             have i₂ := b3e56 X0
             grind)
          | exact superpose b3e56 b3e62
          | exact resolve b3e62 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e75 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e79 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e15
          | exact resolve b3e15 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e82 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e79
        have b3e85 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e82
          | exact resolve b3e82 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e86 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e56 y
             grind)
          | exact superpose b3e56 b3e85
          | exact resolve b3e85 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e85
        have b3e87 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e86
          | exact resolve b3e86 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e199 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e69 x
             grind)
          | exact superpose b3e69 b3e23
          | exact resolve b3e23 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e69
        have b3e352 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e75 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e353 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e352
             have r₂ := b3e20
             grind)
          | exact resolve b3e352 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e352
        have b3e357 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e87
             have i₂ := b3e353
             grind)
          | exact superpose b3e353 b3e87
          | exact resolve b3e87 b3e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87 b3e353
        have b3e361 : False := by grind
        exact b3e361
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e67
          have b4e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e71
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e71
            | exact resolve b4e71 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e75 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e73
            | exact resolve b4e73 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e73
          have b4e76 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e75
            | exact resolve b4e75 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e77 : False := by grind
          exact b4e77
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e66 (σ X0)
               grind)
            | exact superpose b5e66 b5e19
            | exact resolve b5e19 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e70 X0
               have i₂ := b5e66 X0
               grind)
            | exact superpose b5e66 b5e70
            | exact resolve b5e70 b5e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e66 b5e70
          have b5e87 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e131 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e339 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e87 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e340 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e339
               have r₂ := b5e21
               grind)
            | exact resolve b5e339 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e339
          have b5e1616 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e1617 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1616
               have r₂ := b5e23
               grind)
            | exact resolve b5e1616 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1616
          have b5e1618 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1617
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1617
            | exact resolve b5e1617 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1617
          have b5e1619 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1618
               have i₂ := b5e340
               grind)
            | exact superpose b5e340 b5e1618
            | exact resolve b5e1618 b5e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e340 b5e1618
          have b5e1622 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1619
               grind)
            | exact superpose b5e1619 b5e23
            | exact resolve b5e23 b5e1619
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1619
          have b5e1648 : False := by grind
          exact b5e1648
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e51
        have b6e54 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e53
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e53
          | exact resolve b6e53 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e72 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e15
          | exact resolve b6e15 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e75 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e72
        have b6e78 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e75
          | exact resolve b6e75 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e79 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e52 y
             grind)
          | exact superpose b6e52 b6e78
          | exact resolve b6e78 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e78
        have b6e136 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e79
             grind)
          | exact superpose b6e79 b6e13
          | exact resolve b6e13 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e137 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e136
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e136
          | exact resolve b6e136 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e155 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e137
             grind)
          | exact superpose b6e137 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e156 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e155
        have b6e158 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e156
             have r₂ := b6e21
             grind)
          | exact resolve b6e156 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e156
        have b6e160 : False := by grind
        exact b6e160
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e64
          have b7e68 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e67
            | exact resolve b7e67 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e69 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e66 y
               grind)
            | exact superpose b7e66 b7e68
            | exact resolve b7e68 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e66 (σ X0)
               grind)
            | exact superpose b7e66 b7e19
            | exact resolve b7e19 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e71 X0
               have i₂ := b7e66 X0
               grind)
            | exact superpose b7e66 b7e71
            | exact resolve b7e71 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66 b7e71
          have b7e88 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e90 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e88 X0
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e88
            | (have j0 := b7e88 X0
               grind)
            | exact resolve b7e88 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e91 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e23
            | exact resolve b7e23 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e91
            | exact resolve b7e91 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e106 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e690 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e90 (σ x)
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e90
            | (have j0 := b7e90 (σ x)
               grind)
            | (have r₁ := b7e90 (σ x)
               have r₂ := b7e69
               grind)
            | exact resolve b7e90 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69 b7e90
          have b7e691 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e690
          have b7e692 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e691
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e691
            | exact resolve b7e691 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e691
          have b7e693 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e692
               have r₂ := b7e97
               grind)
            | exact resolve b7e692 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e692
          have b7e694 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e693
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e693
            | exact resolve b7e693 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e693
          have b7e695 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e694
               have i₂ := b7e80 x
               grind)
            | exact superpose b7e80 b7e694
            | exact resolve b7e694 b7e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80 b7e694
          have b7e697 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e695
               have i₂ := b7e137 x y
               grind)
            | exact superpose b7e137 b7e695
            | (have j1 := b7e137 x y
               grind)
            | exact resolve b7e695 b7e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137
          have b7e699 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e695
               grind)
            | exact superpose b7e695 b7e14
            | exact resolve b7e14 b7e695
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e695
          have b7e711 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e699
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e699
            | exact resolve b7e699 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e699
          have b7e713 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e697
               have r₂ := b7e97
               grind)
            | exact resolve b7e697 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e697
          have b7e716 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e713
               have r₂ := b7e22
               grind)
            | exact resolve b7e713 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e713
          have b7e717 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e716
               have i₂ := b7e711
               grind)
            | exact superpose b7e711 b7e716
            | exact resolve b7e716 b7e711
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e711 b7e716
          have b7e718 : False := by grind
          exact b7e718
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e123 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1362 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e123 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e1363 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1362
               have r₂ := b8e23
               grind)
            | exact resolve b8e1362 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1362
          have b8e1364 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1363
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1363
            | exact resolve b8e1363 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1363
          have b8e1369 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1364
               grind)
            | exact superpose b8e1364 b8e20
            | exact resolve b8e20 b8e1364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1364
          have b8e1469 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1369
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1369
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1369 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1369
          have b8e1470 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1469
          have b8e1472 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1470
               have r₂ := b8e21
               grind)
            | exact resolve b8e1470 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1470
          have b8e1475 : False := by grind
          exact b8e1475

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pxy_pxx_pyy_pxy_Equation907 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law907 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
      have b0e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e45 (σ X0)
           grind)
        | exact superpose b0e45 b0e17
        | exact resolve b0e17 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e51 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e51
        | exact resolve b0e51 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e51
      have b0e176 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e56 y
           grind)
        | exact superpose b0e56 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e56 y
           grind)
        | exact resolve b0e22 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e56
      have b0e185 : False := by grind
      exact b0e185
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
        have b1e52 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b1e53 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by grind
        clear b1e53
        have b1e57 : (k x y) = (M.op x x) := by grind
        clear b1e52
        have b1e58 : (M.op (σ x) (σ y)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e56
          | exact resolve b1e56 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e55 x
             grind)
          | exact superpose b1e55 b1e58
          | exact resolve b1e58 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e55 (σ X0)
             grind)
          | exact superpose b1e55 b1e18
          | exact resolve b1e18 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e61 X0
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e61
          | exact resolve b1e61 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e61
        have b1e75 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
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
        have b1e77 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e75 X0
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e75
          | (have j0 := b1e75 X0
             grind)
          | exact resolve b1e75 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e133 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e23
          | exact resolve b1e23 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e761 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e77 (σ y)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e77
          | (have j0 := b1e77 (σ y)
             grind)
          | (have r₁ := b1e77 (σ y)
             have r₂ := b1e59
             grind)
          | exact resolve b1e77 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e77
        have b1e768 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e761
        have b1e772 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e768
             have i₂ := b1e68 y
             grind)
          | exact superpose b1e68 b1e768
          | exact resolve b1e768 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e768
        have b1e776 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e772
             have r₂ := b1e133
             grind)
          | exact resolve b1e772 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e772
        have b1e780 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e776
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e776
          | exact resolve b1e776 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e776
        have b1e782 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e780
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e780
          | exact resolve b1e780 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e780
        have b1e784 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e782
             have i₂ := b1e68 y
             grind)
          | exact superpose b1e68 b1e782
          | exact resolve b1e782 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e782
        have b1e786 : False := by grind
        exact b1e786
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e50 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (k x y) = (M.op x x) := by grind
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
        have b2e95 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) X0) ∨ (M.op X0 X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
        have b2e143 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e61 x
             grind)
          | exact superpose b2e61 b2e22
          | exact resolve b2e22 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1400 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e95 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e1401 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1400
             have r₂ := b2e21
             grind)
          | exact resolve b2e1400 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1400
        have b2e1407 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1401
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1401
          | exact resolve b2e1401 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1401
        have b2e1411 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1407
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1407
          | exact resolve b2e1407 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1407
        have b2e1412 : False := by grind
        exact b2e1412
  · rcases eq_or_ne (M.op x x) (M.op x y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
        have b3e53 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e53
        have b3e58 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e56
          | exact resolve b3e56 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e55 (σ X0)
             grind)
          | exact superpose b3e55 b3e18
          | exact resolve b3e18 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e61 X0
             have i₂ := b3e55 X0
             grind)
          | exact superpose b3e55 b3e61
          | exact resolve b3e61 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e75 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op X0 X0) = (M.op x X0) ∨ (M.op X0 X0) = (k x X0) := by
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
        have b3e77 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e15
          | exact resolve b3e15 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e82 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e77
        have b3e85 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e82
          | exact resolve b3e82 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e86 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e55 x
             grind)
          | exact superpose b3e55 b3e85
          | exact resolve b3e85 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e85
        have b3e87 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e86
          | exact resolve b3e86 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e197 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e68 y
             grind)
          | exact superpose b3e68 b3e23
          | exact resolve b3e23 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e68
        have b3e354 : (M.op x y) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e75 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e355 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e354
             have r₂ := b3e20
             grind)
          | exact resolve b3e354 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e354
        have b3e359 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e87
             have i₂ := b3e355
             grind)
          | exact superpose b3e355 b3e87
          | exact resolve b3e87 b3e355
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87 b3e355
        have b3e363 : False := by grind
        exact b3e363
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e69 (σ X0)
               grind)
            | exact superpose b4e69 b4e19
            | exact resolve b4e19 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e71 X0
               have i₂ := b4e69 X0
               grind)
            | exact superpose b4e69 b4e71
            | exact resolve b4e71 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69 b4e71
          have b4e158 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e28
               have i₂ := b4e80 x
               grind)
            | exact superpose b4e80 b4e28
            | (have r₁ := b4e28
               have r₂ := b4e80 x
               grind)
            | exact resolve b4e28 b4e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e80
          have b4e168 : False := by grind
          exact b4e168
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
               have i₂ := b5e65 (σ X0)
               grind)
            | exact superpose b5e65 b5e19
            | exact resolve b5e19 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e67 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e67
            | exact resolve b5e67 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e67
          have b5e84 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e87 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e84
          have b5e88 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e87
               have r₂ := b5e25
               grind)
            | exact resolve b5e87 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e87
          have b5e104 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e144 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e76 y
               grind)
            | exact superpose b5e76 b5e23
            | exact resolve b5e23 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e1394 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e104 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e1395 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1394
               have r₂ := b5e24
               grind)
            | exact resolve b5e1394 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1394
          have b5e1396 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1395
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1395
            | exact resolve b5e1395 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1395
          have b5e1397 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1396
               have i₂ := b5e88
               grind)
            | exact superpose b5e88 b5e1396
            | exact resolve b5e1396 b5e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e88 b5e1396
          have b5e1398 : False := by grind
          exact b5e1398
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e21 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
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
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e75 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e70
        have b6e78 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e75
          | exact resolve b6e75 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e79 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e51 x
             grind)
          | exact superpose b6e51 b6e78
          | exact resolve b6e78 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e78
        have b6e136 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e79
             grind)
          | exact superpose b6e79 b6e13
          | exact resolve b6e13 b6e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e137 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e136
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e136
          | exact resolve b6e136 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e136
        have b6e154 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e137
             grind)
          | exact superpose b6e137 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e137
        have b6e155 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e154
        have b6e157 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e155
             have r₂ := b6e21
             grind)
          | exact resolve b6e155 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e155
        have b6e159 : False := by grind
        exact b6e159
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e65 (σ X0)
               grind)
            | exact superpose b7e65 b7e19
            | exact resolve b7e19 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e67 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e67
          have b7e85 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e87 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e85
          have b7e88 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e25
               grind)
            | exact resolve b7e87 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e87
          have b7e89 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e88
            | exact resolve b7e88 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e90 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e76 y
               grind)
            | exact superpose b7e76 b7e89
            | exact resolve b7e89 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e89
          have b7e95 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e14
            | exact resolve b7e14 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e96 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e95
            | exact resolve b7e95 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e155 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e156 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e155
          have b7e158 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e156
               have r₂ := b7e21
               grind)
            | exact resolve b7e156 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e156
          have b7e160 : False := by grind
          exact b7e160
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e111 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1277 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e111 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111
          have b8e1278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1277
               have r₂ := b8e24
               grind)
            | exact resolve b8e1277 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1277
          have b8e1279 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1278
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1278
            | exact resolve b8e1278 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1278
          have b8e1283 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1279
               grind)
            | exact superpose b8e1279 b8e20
            | exact resolve b8e20 b8e1279
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1279
          have b8e1344 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e1283
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1283
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1283 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1283
          have b8e1345 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e1344
          have b8e1347 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e1345
               have r₂ := b8e21
               grind)
            | exact resolve b8e1345 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1345
          have b8e1350 : False := by grind
          exact b8e1350

/-- `Equation907`: `x = y ◇ ((y ◇ x) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pxx_pyy_pyx_Equation907 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law907 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law907.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X0 X1))) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op y x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : x = (M.op y (M.op (M.op y y) (M.op x y))) := by
        first
        | (have i₁ := b0e11 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear b0e43
      have b0e46 : (k x y) = (M.op x x) := by grind
      clear b0e41
      have b0e47 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e45
        | exact resolve b0e45 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e48 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
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
      have b0e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e17
        | exact resolve b0e17 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e50 X0
           have i₂ := b0e44 X0
           grind)
        | exact superpose b0e44 b0e50
        | exact resolve b0e50 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e50
      have b0e77 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X0))) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X0
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X1
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1109 : (σ x) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e77 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e77
        | (have j0 := b0e77 (σ y) (σ x)
           grind)
        | exact resolve b0e77 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1113 : x = (M.op y (M.op (M.op y y) (M.op y y))) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e77 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e77
        | (have j0 := b0e77 y x
           grind)
        | exact resolve b0e77 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1148 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 (M.op (M.op X1 X0) (M.op X1 X1))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X1 X0
           have i₂ := b0e77 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e77 X0 X1
           grind)
        | exact superpose b0e77 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e77 X1 X0
           grind)
        | (have r₁ := b0e14 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X0)) X0
           have r₂ := b0e77 X0 (M.op X0 X0)
           grind)
        | (have r₁ := b0e14 X0 X1
           have r₂ := b0e77 X0 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e77 X0 X0
           grind)
        | exact resolve b0e14 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e1190 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X1 X1))) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e1148 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1148
      have b0e1193 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e1113
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e1113
        | exact resolve b0e1113 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1113
      have b0e1197 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1109
           have i₂ := b0e11 (σ y) (σ y)
           grind)
        | exact superpose b0e11 b0e1109
        | exact resolve b0e1109 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1109
      have b0e1203 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1197
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e1197
        | exact resolve b0e1197 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1197
      have b0e1207 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e1203
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e1203
        | exact resolve b0e1203 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1203
      have b0e7906 : (σ x) = (M.op (σ y) (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e1190 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1190
        | (have j0 := b0e1190 (σ x) (σ y)
           grind)
        | exact resolve b0e1190 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e7918 : x = (M.op y (M.op (M.op y y) (M.op y y))) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e1190 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1190
        | (have j0 := b0e1190 x y
           grind)
        | exact resolve b0e1190 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1190
      have b0e8051 : (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e7918
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e7918
        | exact resolve b0e7918 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7918
      have b0e8060 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e7906
           have i₂ := b0e11 (σ y) (σ y)
           grind)
        | exact superpose b0e11 b0e7906
        | exact resolve b0e7906 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7906
      have b0e8083 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8060
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8060
        | exact resolve b0e8060 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8060
      have b0e8094 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e8083
           have i₂ := b0e55 y
           grind)
        | exact superpose b0e55 b0e8083
        | exact resolve b0e8083 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8083
      have b0e8104 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8094
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8094
        | exact resolve b0e8094 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8094
      have b0e8123 : (M.op x y) ≠ (M.op y y) ∨ (M.op y y) = (k y x) ∨ x = y := by grind
      have b0e8141 : (M.op (σ y) (σ y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e1207
           grind)
        | exact superpose b0e1207 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | exact resolve b0e15 b0e1207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8167 : (σ (M.op x x)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by grind
      clear b0e1207
      have b0e8179 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8141
           have i₂ := b0e55 y
           grind)
        | exact superpose b0e55 b0e8141
        | exact resolve b0e8141 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8141
      have b0e8198 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8179
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e8179
        | exact resolve b0e8179 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8179
      have b0e8211 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8198
           have r₂ := b0e8167
           grind)
        | exact resolve b0e8198 b0e8167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8198
      have b0e8216 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8211
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e8211
        | exact resolve b0e8211 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8211
      have b0e8219 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e8216
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e8216
        | exact resolve b0e8216 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e8216
      have b0e8220 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e8219
           have r₂ := b0e8167
           grind)
        | exact resolve b0e8219 b0e8167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8167 b0e8219
      have b0e39707 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e8104
           grind)
        | exact superpose b0e8104 b0e18
        | exact resolve b0e18 b0e8104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8104
      have b0e41113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e39707
           have i₂ := b0e8051
           grind)
        | exact superpose b0e8051 b0e39707
        | exact resolve b0e39707 b0e8051
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8051
      have b0e41114 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e39707
           have i₂ := b0e1193
           grind)
        | exact superpose b0e1193 b0e39707
        | exact resolve b0e39707 b0e1193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1193 b0e39707
      have b0e41137 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
      clear b0e41114
      have b0e41138 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by grind
      clear b0e41113
      have b0e43735 : (M.op x y) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e41137
           grind)
        | exact superpose b0e41137 b0e12
        | exact resolve b0e12 b0e41137
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41137
      have b0e43805 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e43735
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e43735
        | exact resolve b0e43735 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43735
      have b0e45198 : (M.op x y) = (τ (σ (M.op y y))) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e12 (M.op x y)
           have i₂ := b0e41138
           grind)
        | exact superpose b0e41138 b0e12
        | exact resolve b0e12 b0e41138
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41138
      have b0e45268 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e45198
           have i₂ := b0e12 (M.op y y)
           grind)
        | exact superpose b0e12 b0e45198
        | exact resolve b0e45198 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45198
      have b0e45269 : (M.op y y) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have r₁ := b0e45268
           have r₂ := b0e8123
           grind)
        | exact resolve b0e45268 b0e8123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8123 b0e45268
      have b0e45908 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e8220
           have i₂ := b0e45269
           grind)
        | exact superpose b0e45269 b0e8220
        | exact resolve b0e8220 b0e45269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8220 b0e45269
      have b0e45945 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e45908
      have b0e45946 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
      clear b0e45945
      have b0e45982 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e45946
           grind)
        | exact superpose b0e45946 b0e18
        | exact resolve b0e18 b0e45946
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45946
      have b0e46865 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
        first
        | (have i₁ := b0e45982
           have i₂ := b0e43805
           grind)
        | exact superpose b0e43805 b0e45982
        | exact resolve b0e45982 b0e43805
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43805 b0e45982
      have b0e46867 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e46865
      have b0e46868 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e46867
      have b0e47006 : x = (M.op y (M.op (M.op y y) (M.op y y))) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e46868
           grind)
        | exact superpose b0e46868 b0e23
        | exact resolve b0e23 b0e46868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e46868
      have b0e47066 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e47006
           have i₂ := b0e11 y y
           grind)
        | exact superpose b0e11 b0e47006
        | exact resolve b0e47006 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47006
      have b0e47067 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e47066
      have b0e47240 : x = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e47067
           grind)
        | exact superpose b0e47067 b0e12
        | exact resolve b0e12 b0e47067
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47067
      have b0e47307 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e47240
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e47240
        | exact resolve b0e47240 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47240
      have b0e47308 : x = y := by grind
      clear b0e47307
      have b0e47883 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e47308
           grind)
        | exact superpose b0e47308 b0e18
        | exact resolve b0e18 b0e47308
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47308
      have b0e47934 : False := by grind
      exact b0e47934
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op y x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e51 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b1e53 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : (M.op (σ y) (σ x)) = (k (σ x) (σ x)) := by grind
        clear b1e53
        have b1e57 : (k x y) = (M.op x x) := by grind
        clear b1e51
        have b1e58 : (M.op (σ y) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e56
          | exact resolve b1e56 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e55 x
             grind)
          | exact superpose b1e55 b1e58
          | exact resolve b1e58 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e55 (σ X0)
             grind)
          | exact superpose b1e55 b1e18
          | exact resolve b1e18 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e68 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e61 X0
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e61
          | exact resolve b1e61 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e61
        have b1e74 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
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
        have b1e76 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e74 X0
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e74
          | (have j0 := b1e74 X0
             grind)
          | exact resolve b1e74 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e131 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e21
          | exact resolve b1e21 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e136 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e131
             have i₂ := b1e68 y
             grind)
          | exact superpose b1e68 b1e131
          | exact resolve b1e131 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131
        have b1e773 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e76 (σ y)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e76
          | (have j0 := b1e76 (σ y)
             grind)
          | (have r₁ := b1e76 (σ y)
             have r₂ := b1e59
             grind)
          | exact resolve b1e76 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e76
        have b1e774 : (M.op (σ y) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b1e773
        have b1e775 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e774
             have i₂ := b1e68 y
             grind)
          | exact superpose b1e68 b1e774
          | exact resolve b1e774 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e774
        have b1e776 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e775
             have r₂ := b1e136
             grind)
          | exact resolve b1e775 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775
        have b1e777 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e776
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e776
          | exact resolve b1e776 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e776
        have b1e778 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e777
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e777
          | exact resolve b1e777 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e777
        have b1e779 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e778
             have i₂ := b1e68 y
             grind)
          | exact superpose b1e68 b1e778
          | exact resolve b1e778 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e778
        have b1e780 : False := by grind
        exact b1e780
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op y x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e49 : (M.op y y) ≠ (M.op y y) ∨ (k x y) = (M.op x x) := by
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (k x y) = (M.op x x) := by grind
        clear b2e49
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
        have b2e94 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
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
        have b2e142 : (M.op (σ y) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e61 x
             grind)
          | exact superpose b2e61 b2e22
          | exact resolve b2e22 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1405 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e94 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e1406 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1405
             have r₂ := b2e21
             grind)
          | exact resolve b2e1405 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1405
        have b2e1407 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1406
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1406
          | exact resolve b2e1406 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1406
        have b2e1408 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1407
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1407
          | exact resolve b2e1407 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1407
        have b2e1409 : False := by grind
        exact b2e1409
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b3e21 : (M.op y x) = (M.op x x) := by grind
        have b3e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e53 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e53
        have b3e58 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e56
          | exact resolve b3e56 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e74 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 x) ∨ (M.op X0 X0) = (M.op X0 x) ∨ (M.op X0 X0) = (k x X0) := by
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
        have b3e78 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e15
          | exact resolve b3e15 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e81 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e78
        have b3e84 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e81
          | exact resolve b3e81 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e85 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e55 x
             grind)
          | exact superpose b3e55 b3e84
          | exact resolve b3e84 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55 b3e84
        have b3e86 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e85
          | exact resolve b3e85 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e140 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e86
             grind)
          | exact superpose b3e86 b3e13
          | exact resolve b3e13 b3e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e86
        have b3e141 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e140
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e140
          | exact resolve b3e140 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e140
        have b3e374 : (M.op y x) = (M.op y y) ∨ (M.op y y) = (k x y) := by
          first
          | (have j0 := b3e74 y
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e375 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e374
             have r₂ := b3e20
             grind)
          | exact resolve b3e374 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e374
        have b3e378 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e141
             have i₂ := b3e375
             grind)
          | exact superpose b3e375 b3e141
          | exact resolve b3e141 b3e375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141 b3e375
        have b3e383 : False := by grind
        exact b3e383
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X0) (M.op X0 X1))) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b4e22 : (M.op y x) = (M.op x x) := by grind
          have b4e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (M.op y y) ≠ (M.op x x) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b4e42 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e28 X1 X0
               grind)
            | exact superpose b4e28 b4e14
            | exact resolve b4e14 b4e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b4e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e68 (σ X0)
               grind)
            | exact superpose b4e68 b4e19
            | exact resolve b4e19 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e28 X0 (τ X0)
               have i₂ := b4e68 (τ X0)
               grind)
            | exact superpose b4e68 b4e28
            | exact resolve b4e28 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e73 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e73
            | exact resolve b4e73 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e70 X0
               have i₂ := b4e68 X0
               grind)
            | exact superpose b4e68 b4e70
            | exact resolve b4e70 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e82 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e76 X0
               have i₂ := b4e68 X0
               grind)
            | exact superpose b4e68 b4e76
            | exact resolve b4e76 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68 b4e76
          have b4e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X1 X0))) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e13 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e130 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e135 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102
          have b4e138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e125 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e125
            | (have j0 := b4e125 X0 X1
               grind)
            | exact resolve b4e125 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125
          have b4e142 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               have j1 := b4e130 X1 X0
               grind)
            | (have r₁ := b4e133 X0 X1
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e133 X1 X0
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e133 X0 X0
               have r₂ := b4e130 X0 X0
               grind)
            | exact resolve b4e133 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e133
          have b4e146 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e138 X0 X1
               have i₂ := b4e79 X1
               grind)
            | exact superpose b4e79 b4e138
            | (have j0 := b4e138 X0 X1
               grind)
            | exact resolve b4e138 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e138
          have b4e153 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e79 y
               grind)
            | exact superpose b4e79 b4e25
            | exact resolve b4e25 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e159 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e17
            | (have j0 := b4e17 (σ X0) X1
               grind)
            | exact resolve b4e17 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e160 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (σ X0)
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e16
            | (have j0 := b4e16 X1 (σ X0)
               grind)
            | exact resolve b4e16 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e165 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e153
               have i₂ := b4e79 x
               grind)
            | exact superpose b4e79 b4e153
            | exact resolve b4e153 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153
          have b4e182 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e14
            | exact resolve b4e14 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e240 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 (τ X0)
               have i₂ := b4e182 X0
               grind)
            | exact superpose b4e182 b4e16
            | (have j0 := b4e16 X1 (τ X0)
               grind)
            | exact resolve b4e16 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e515 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X1 X0
               have i₂ := b4e135 (τ X1) X0
               grind)
            | exact superpose b4e135 b4e28
            | (have j1 := b4e135 (τ X1) X0
               grind)
            | exact resolve b4e28 b4e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135
          have b4e698 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e28 X0 X1
               have i₂ := b4e142 X1 (τ X0)
               grind)
            | exact superpose b4e142 b4e28
            | (have j1 := b4e142 X1 (τ X0)
               grind)
            | exact resolve b4e28 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28
          have b4e716 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X1 X0
               have i₂ := b4e142 (τ X1) X0
               grind)
            | exact superpose b4e142 b4e27
            | (have j1 := b4e142 (τ X1) X0
               grind)
            | exact resolve b4e27 b4e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e742 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e698 X0 X1
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e698
            | (have j0 := b4e698 X0 X1
               grind)
            | exact resolve b4e698 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e698
          have b4e771 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e742 X0 X1
               have i₂ := b4e182 X0
               grind)
            | exact superpose b4e182 b4e742
            | (have j0 := b4e742 X0 X1
               grind)
            | exact resolve b4e742 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e742
          have b4e979 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e104 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e104
            | (have j0 := b4e104 (σ x) (σ y)
               grind)
            | exact resolve b4e104 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e985 : y = (M.op x (M.op (M.op x x) (M.op x x))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e104 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e104
            | (have j0 := b4e104 x y
               grind)
            | exact resolve b4e104 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1010 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e104 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e104 X0 X1
               grind)
            | exact superpose b4e104 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e104 X1 X0
               grind)
            | (have r₁ := b4e17 X1 X0
               have r₂ := b4e104 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e104 X0 X0
               grind)
            | exact resolve b4e17 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e1045 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X0 X1))) = X0 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e1010 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1010
          have b4e1049 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e985
               have i₂ := b4e13 x x
               grind)
            | exact superpose b4e13 b4e985
            | exact resolve b4e985 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e985
          have b4e1054 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e979
               have i₂ := b4e13 (σ x) (σ x)
               grind)
            | exact superpose b4e13 b4e979
            | exact resolve b4e979 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e979
          have b4e1062 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1054
               have i₂ := b4e79 y
               grind)
            | exact superpose b4e79 b4e1054
            | exact resolve b4e1054 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1054
          have b4e1067 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e1062
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e1062
            | exact resolve b4e1062 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1062
          have b4e2810 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e160 X1 (σ X0)
               have i₂ := b4e146 X1 X0
               grind)
            | exact superpose b4e146 b4e160
            | (have j0 := b4e160 X1 (σ X0)
               have j1 := b4e146 X1 X0
               grind)
            | (have r₁ := b4e160 X0 (σ X0)
               have r₂ := b4e146 X0 X0
               grind)
            | (have r₁ := b4e160 X0 (σ X1)
               have r₂ := b4e146 X0 X1
               grind)
            | exact resolve b4e160 b4e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2867 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2868 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146
          have b4e2937 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e2810 X0 X1
               have j1 := b4e160 X1 (σ X0)
               grind)
            | (have r₁ := b4e2810 X0 X0
               have r₂ := b4e160 X0 (σ X0)
               grind)
            | (have r₁ := b4e2810 X0 X0
               have r₂ := b4e160 X0 (σ X0)
               grind)
            | exact resolve b4e2810 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160 b4e2810
          have b4e3031 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2937 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e2937
            | (have j0 := b4e2937 X0 X1
               grind)
            | exact resolve b4e2937 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2937
          have b4e3091 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e3031 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e3031
            | (have j0 := b4e3031 X0 X1
               grind)
            | exact resolve b4e3031 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3031
          have b4e8687 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by grind
          have b4e10433 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (k X0 (τ (σ X1))) = (M.op (τ (σ X1)) X0) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e515 X0 (σ X1)
               grind)
            | exact superpose b4e515 b4e19
            | (have j1 := b4e515 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e515
          have b4e10554 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10433 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e10433
            | (have j0 := b4e10433 X0 X1
               grind)
            | exact resolve b4e10433 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10433
          have b4e10603 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10554 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e10554
            | (have j0 := b4e10554 X0 X1
               grind)
            | exact resolve b4e10554 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10554
          have b4e13444 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e716 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e716
            | exact resolve b4e716 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e716
          have b4e13780 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13444 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e13444
            | (have j0 := b4e13444 X0 X1
               grind)
            | exact resolve b4e13444 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13444
          have b4e14422 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e240 X0 X1
               have i₂ := b4e771 X0 X1
               grind)
            | exact superpose b4e771 b4e240
            | (have j0 := b4e240 X0 X1
               have j1 := b4e771 X0 X1
               grind)
            | (have r₁ := b4e240 X0 X1
               have r₂ := b4e771 X0 X1
               grind)
            | exact resolve b4e240 b4e771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e771
          have b4e14692 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b4e14422 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14422
          have b4e30471 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2867 (τ X1) (τ X0)
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e2867
            | (have j0 := b4e2867 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2867 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2867
          have b4e30597 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30471 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e30471
            | (have j0 := b4e30471 X0 X1
               grind)
            | exact resolve b4e30471 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30471
          have b4e30642 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30597 X0 X1
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e30597
            | (have j0 := b4e30597 X0 X1
               grind)
            | exact resolve b4e30597 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30597
          have b4e30679 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30642 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30642
            | (have j0 := b4e30642 X0 X1
               grind)
            | exact resolve b4e30642 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30642
          have b4e30709 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30679 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30679
            | (have j0 := b4e30679 X0 X1
               grind)
            | exact resolve b4e30679 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30679
          have b4e30734 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30709 X0 X1
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e30709
            | (have j0 := b4e30709 X0 X1
               grind)
            | exact resolve b4e30709 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30709
          have b4e30755 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e30734 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30734
            | (have j0 := b4e30734 X0 X1
               grind)
            | exact resolve b4e30734 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30734
          have b4e30772 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e30755 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e30755
            | (have j0 := b4e30755 X0 X1
               grind)
            | exact resolve b4e30755 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30755
          have b4e30785 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30772 X0 X1
               have i₂ := b4e82 X1
               grind)
            | exact superpose b4e82 b4e30772
            | (have j0 := b4e30772 X0 X1
               grind)
            | exact resolve b4e30772 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30772
          have b4e30973 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2868 (τ X1) (τ X0)
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e2868
            | (have j0 := b4e2868 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2868 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e31101 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30973 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e30973
            | (have j0 := b4e30973 X0 X1
               grind)
            | exact resolve b4e30973 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30973
          have b4e31149 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e31101 X0 X1
               have i₂ := b4e82 X1
               grind)
            | exact superpose b4e82 b4e31101
            | (have j0 := b4e31101 X0 X1
               grind)
            | exact resolve b4e31101 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31101
          have b4e31185 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e31149 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31149
            | (have j0 := b4e31149 X0 X1
               grind)
            | exact resolve b4e31149 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31149
          have b4e31212 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e31185 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e31185
            | (have j0 := b4e31185 X0 X1
               grind)
            | exact resolve b4e31185 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31185
          have b4e31235 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e31212 X0 X1
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e31212
            | (have j0 := b4e31212 X0 X1
               grind)
            | exact resolve b4e31212 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31212
          have b4e31257 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e31235 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31235
            | (have j0 := b4e31235 X0 X1
               grind)
            | exact resolve b4e31235 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31235
          have b4e31274 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e31257 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e31257
            | (have j0 := b4e31257 X0 X1
               grind)
            | exact resolve b4e31257 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31257
          have b4e31287 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e31274 X0 X1
               have i₂ := b4e82 X1
               grind)
            | exact superpose b4e82 b4e31274
            | (have j0 := b4e31274 X0 X1
               grind)
            | exact resolve b4e31274 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31274
          have b4e37681 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1045 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1045
            | (have j0 := b4e1045 (σ y) (σ x)
               grind)
            | exact resolve b4e1045 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37699 : y = (M.op x (M.op (M.op x x) (M.op x x))) ∨ (M.op y y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e1045 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1045
            | (have j0 := b4e1045 y x
               grind)
            | exact resolve b4e1045 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1045
          have b4e38459 : y = (M.op x (M.op (M.op x x) (M.op x x))) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have r₁ := b4e37699
               have r₂ := b4e26
               grind)
            | exact resolve b4e37699 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37699
          have b4e38473 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b4e37681
               have r₂ := b4e25
               grind)
            | exact resolve b4e37681 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37681
          have b4e38548 : (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e38459
               have i₂ := b4e13 x x
               grind)
            | exact superpose b4e13 b4e38459
            | exact resolve b4e38459 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38459
          have b4e38557 : (σ x) = (σ y) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38473
               have i₂ := b4e13 (σ x) (σ x)
               grind)
            | exact superpose b4e13 b4e38473
            | exact resolve b4e38473 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38473
          have b4e38614 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38557
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38557
            | exact resolve b4e38557 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38557
          have b4e38649 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b4e38614
               have i₂ := b4e79 x
               grind)
            | exact superpose b4e79 b4e38614
            | exact resolve b4e38614 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38614
          have b4e38676 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e38649
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38649
            | exact resolve b4e38649 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38649
          have b4e38810 : (M.op x y) ≠ (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by grind
          clear b4e38548
          have b4e39884 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e38676
               grind)
            | exact superpose b4e38676 b4e20
            | exact resolve b4e20 b4e38676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39896 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e159 y (σ x)
               have i₂ := b4e38676
               grind)
            | exact superpose b4e38676 b4e159
            | (have j0 := b4e159 y (σ x)
               grind)
            | exact resolve b4e159 b4e38676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e159 b4e38676
          have b4e39968 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39896
               have i₂ := b4e79 x
               grind)
            | exact superpose b4e79 b4e39896
            | exact resolve b4e39896 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39896
          have b4e39969 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b4e39968
          have b4e39997 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39969
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e39969
            | exact resolve b4e39969 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39969
          have b4e40011 : (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e39997
               have i₂ := b4e79 x
               grind)
            | exact superpose b4e79 b4e39997
            | exact resolve b4e39997 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39997
          have b4e40012 : (σ (M.op y y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b4e40011
          have b4e41428 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e40012
               have i₂ := b4e10603 y x
               grind)
            | exact superpose b4e10603 b4e40012
            | (have j1 := b4e10603 y x
               grind)
            | (have r₁ := b4e40012
               have r₂ := b4e10603 y x
               grind)
            | exact resolve b4e40012 b4e10603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10603
          have b4e41429 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e41428
          have b4e41431 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b4e41429
               have r₂ := b4e165
               grind)
            | exact resolve b4e41429 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41429
          have b4e42203 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e39884
               have i₂ := b4e41431
               grind)
            | exact superpose b4e41431 b4e39884
            | exact resolve b4e39884 b4e41431
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42214 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e42203
          have b4e42215 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e42214
          have b4e42816 : (M.op x y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e42215
               grind)
            | exact superpose b4e42215 b4e14
            | exact resolve b4e14 b4e42215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42215
          have b4e42889 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e42816
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e42816
            | exact resolve b4e42816 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42816
          have b4e43487 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e42889
               grind)
            | exact superpose b4e42889 b4e165
            | exact resolve b4e165 b4e42889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42889
          have b4e74278 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 (τ X1)
               have i₂ := b4e14692 X1 (τ X0)
               grind)
            | exact superpose b4e14692 b4e27
            | (have j1 := b4e14692 X1 (τ X0)
               grind)
            | exact resolve b4e27 b4e14692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e74663 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (σ X1) X0
               have i₂ := b4e14692 (σ X0) X1
               grind)
            | exact superpose b4e14692 b4e32
            | (have j1 := b4e14692 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e14692
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14692
          have b4e74875 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e74663 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e74663
            | (have j0 := b4e74663 X0 X1
               grind)
            | exact resolve b4e74663 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74663
          have b4e75032 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e74278 X0 X1
               have i₂ := b4e82 X0
               grind)
            | exact superpose b4e82 b4e74278
            | (have j0 := b4e74278 X0 X1
               grind)
            | exact resolve b4e74278 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82 b4e74278
          have b4e75269 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e74875 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e74875
            | (have j0 := b4e74875 X0 X1
               grind)
            | exact resolve b4e74875 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74875
          have b4e75348 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e75032 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e75032
            | (have j0 := b4e75032 X0 X1
               grind)
            | exact resolve b4e75032 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75032
          have b4e75486 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e75269 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e75269
            | (have j0 := b4e75269 X0 X1
               grind)
            | exact resolve b4e75269 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75269
          have b4e75550 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e75348 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e75348
            | (have j0 := b4e75348 X0 X1
               grind)
            | exact resolve b4e75348 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75348
          have b4e75642 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e75486 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e75486
            | (have j0 := b4e75486 X0 X1
               grind)
            | exact resolve b4e75486 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75486
          have b4e75694 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e75550 X0 X1
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e75550
            | (have j0 := b4e75550 X0 X1
               grind)
            | exact resolve b4e75550 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75550
          have b4e75741 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e75642 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e75642
            | (have j0 := b4e75642 X0 X1
               grind)
            | exact resolve b4e75642 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75642
          have b4e77116 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e40012
               have i₂ := b4e75741 x y
               grind)
            | exact superpose b4e75741 b4e40012
            | (have j1 := b4e75741 x y
               grind)
            | exact resolve b4e40012 b4e75741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40012
          have b4e77432 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X1 X0
               have i₂ := b4e75741 (σ X0) X1
               grind)
            | exact superpose b4e75741 b4e32
            | (have j1 := b4e75741 (σ X0) X1
               grind)
            | exact resolve b4e32 b4e75741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e77614 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e75741 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75741
          have b4e77664 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e77116
          have b4e77894 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e77432 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e77432
            | (have j0 := b4e77432 X0 X1
               grind)
            | exact resolve b4e77432 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77432
          have b4e77964 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e77664
               have r₂ := b4e165
               grind)
            | exact resolve b4e77664 b4e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77664
          have b4e78497 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e77894 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e77894
            | (have j0 := b4e77894 X0 X1
               grind)
            | exact resolve b4e77894 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77894
          have b4e82429 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e39884
               have i₂ := b4e77964
               grind)
            | exact superpose b4e77964 b4e39884
            | exact resolve b4e39884 b4e77964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39884
          have b4e82440 : (M.op x y) ≠ (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e77964
          have b4e82445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e82429
          have b4e82446 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by grind
          clear b4e82445
          have b4e87655 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e43487
               have i₂ := b4e82446
               grind)
            | exact superpose b4e82446 b4e43487
            | (have r₁ := b4e43487
               have r₂ := b4e82446
               grind)
            | exact resolve b4e43487 b4e82446
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43487 b4e82446
          have b4e87763 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e87655
          have b4e87764 : (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e87763
          have b4e87837 : (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e87764
               have r₂ := b4e82440
               grind)
            | exact resolve b4e87764 b4e82440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82440 b4e87764
          have b4e102046 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e75694 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e75694
            | (have j1 := b4e18 X1 X0
               grind)
            | exact resolve b4e75694 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e103076 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e30785 X0 X1
               have i₂ := b4e75694 X0 X1
               grind)
            | exact superpose b4e75694 b4e30785
            | (have j0 := b4e30785 X0 X1
               have j1 := b4e75694 X0 X1
               grind)
            | (have r₁ := b4e30785 X1 X1
               have r₂ := b4e75694 X1 X1
               grind)
            | (have r₁ := b4e30785 X0 X1
               have r₂ := b4e75694 X0 X1
               grind)
            | exact resolve b4e30785 b4e75694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e103580 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e103076 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103076
          have b4e103863 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e102046 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102046
          have b4e104189 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e103580 X0 X1
               have j1 := b4e31287 X0 X1
               grind)
            | (have r₁ := b4e103580 X0 X1
               have r₂ := b4e31287 X0 X1
               grind)
            | exact resolve b4e103580 b4e31287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103580
          have b4e111103 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e103863 X1 X0
               have i₂ := b4e75694 X0 X1
               grind)
            | exact superpose b4e75694 b4e103863
            | (have j0 := b4e103863 X1 X0
               have j1 := b4e75694 X0 X1
               grind)
            | exact resolve b4e103863 b4e75694
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111668 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e75694 X1 X0
               have i₂ := b4e103863 X0 X1
               grind)
            | exact superpose b4e103863 b4e75694
            | (have j0 := b4e75694 X1 X0
               have j1 := b4e103863 X0 X1
               grind)
            | exact resolve b4e75694 b4e103863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75694
          have b4e111796 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e103863 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e103863 X0 X1
               grind)
            | exact superpose b4e103863 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e103863 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e103863 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e103863 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X0
               have r₂ := b4e103863 X0 X1
               grind)
            | exact resolve b4e16 b4e103863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e103863
          have b4e112250 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e111796 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111796
          have b4e112522 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e111668 X0 X1
               have j1 := b4e77614 X1 X0
               grind)
            | (have r₁ := b4e111668 X1 X0
               have r₂ := b4e77614 X0 X1
               grind)
            | (have r₁ := b4e111668 X1 X1
               have r₂ := b4e77614 X1 X1
               grind)
            | (have r₁ := b4e111668 X0 X0
               have r₂ := b4e77614 X0 X0
               grind)
            | exact resolve b4e111668 b4e77614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77614 b4e111668
          have b4e112707 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e111103 X0 X1
               have j1 := b4e31287 X0 X1
               grind)
            | (have r₁ := b4e111103 X0 X1
               have r₂ := b4e31287 X0 X1
               grind)
            | (have r₁ := b4e111103 X1 X1
               have r₂ := b4e31287 X1 X1
               grind)
            | exact resolve b4e111103 b4e31287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31287 b4e111103
          have b4e112863 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e112522 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e112522 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e112522 X0 X0
               have r₂ := b4e16 X0 X0
               grind)
            | exact resolve b4e112522 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112522
          have b4e112952 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112707 X0 X1
               have j1 := b4e30785 X0 X1
               grind)
            | (have r₁ := b4e112707 X0 X1
               have r₂ := b4e30785 X0 X1
               grind)
            | exact resolve b4e112707 b4e30785
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30785 b4e112707
          have b4e118690 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e112863 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112863
          have b4e120753 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e112952 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e112952 X0 X1
               grind)
            | exact superpose b4e112952 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e112952 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e112952 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e112952 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e112952 X0 X0
               grind)
            | exact resolve b4e17 b4e112952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121190 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e112952 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e112952 X0 X1
               grind)
            | exact superpose b4e112952 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e112952 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e112952 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e112952 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e112952 X0 X1
               grind)
            | exact resolve b4e16 b4e112952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112952
          have b4e121655 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e121190 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121190
          have b4e121691 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e120753 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120753
          have b4e121946 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e121691 X0 X1
               have j1 := b4e118690 X0 X1
               grind)
            | (have r₁ := b4e121691 X0 X1
               have r₂ := b4e118690 X0 X1
               grind)
            | (have r₁ := b4e121691 X1 X0
               have r₂ := b4e118690 X0 X1
               grind)
            | (have r₁ := b4e121691 X0 X0
               have r₂ := b4e118690 X0 X0
               grind)
            | exact resolve b4e121691 b4e118690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118690 b4e121691
          have b4e127403 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e121655 x y
               have i₂ := b4e87837
               grind)
            | exact superpose b4e87837 b4e121655
            | (have j0 := b4e121655 x y
               grind)
            | exact resolve b4e121655 b4e87837
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87837 b4e121655
          have b4e128706 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e127403
               have r₂ := b4e26
               grind)
            | exact resolve b4e127403 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127403
          have b4e135547 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X1 X0
               have i₂ := b4e104189 X1 X0
               grind)
            | (have i₁ := b4e16 X1 X1
               have i₂ := b4e104189 X0 X1
               grind)
            | exact superpose b4e104189 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e104189 X1 X0
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e104189 X0 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e104189 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e104189 X0 X1
               grind)
            | exact resolve b4e16 b4e104189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104189
          have b4e136190 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e135547 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e135547
          have b4e139491 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X1) ∨ (M.op (τ X1) (τ X0)) = (τ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e112250 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112250
          have b4e151864 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (k X0 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e136190 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136190
          have b4e156885 : (M.op x y) ≠ (M.op x y) ∨ (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e139491 y x
               have i₂ := b4e41431
               grind)
            | exact superpose b4e41431 b4e139491
            | (have j0 := b4e139491 y x
               grind)
            | (have r₁ := b4e139491 y x
               have r₂ := b4e41431
               grind)
            | exact resolve b4e139491 b4e41431
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e139491
          have b4e156892 : (M.op x y) ≠ (M.op x y) ∨ (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e156885
          have b4e156893 : (τ (M.op x y)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e156892
          have b4e158560 : (τ (M.op x x)) ≠ (τ (M.op x y)) ∨ (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e240 x (τ y)
               have i₂ := b4e156893
               grind)
            | exact superpose b4e156893 b4e240
            | (have j0 := b4e240 x (τ y)
               grind)
            | exact resolve b4e240 b4e156893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156893
          have b4e158736 : (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e158560
               have r₂ := b4e128706
               grind)
            | exact resolve b4e158560 b4e128706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128706 b4e158560
          have b4e158813 : (τ (k y x)) = (M.op (τ y) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e158736
               have i₂ := b4e47 x y
               grind)
            | exact superpose b4e47 b4e158736
            | exact resolve b4e158736 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e158736
          have b4e158860 : (τ (M.op y y)) = (τ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e158813
               have i₂ := b4e182 y
               grind)
            | exact superpose b4e182 b4e158813
            | exact resolve b4e158813 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e158813
          have b4e161154 : (k y x) = (σ (τ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e15 (k y x)
               have i₂ := b4e158860
               grind)
            | exact superpose b4e158860 b4e15
            | exact resolve b4e15 b4e158860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e158860
          have b4e161340 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e161154
               have i₂ := b4e15 (M.op y y)
               grind)
            | exact superpose b4e15 b4e161154
            | exact resolve b4e161154 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e161154
          have b4e163635 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e41431
               have i₂ := b4e161340
               grind)
            | exact superpose b4e161340 b4e41431
            | exact resolve b4e41431 b4e161340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41431 b4e161340
          have b4e163817 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by grind
          clear b4e163635
          have b4e226291 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e42 X0 (σ X1)
               have i₂ := b4e78497 X1 (σ X0)
               grind)
            | exact superpose b4e78497 b4e42
            | (have j1 := b4e78497 X1 (σ X0)
               grind)
            | exact resolve b4e42 b4e78497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e78497
          have b4e226356 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e226291 X0 X1
               have i₂ := b4e79 X0
               grind)
            | exact superpose b4e79 b4e226291
            | (have j0 := b4e226291 X0 X1
               grind)
            | exact resolve b4e226291 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79 b4e226291
          have b4e226385 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e226356 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e226356
            | (have j0 := b4e226356 X0 X1
               grind)
            | exact resolve b4e226356 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226356
          have b4e226402 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e226385 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e226385
            | (have j0 := b4e226385 X0 X1
               grind)
            | exact resolve b4e226385 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226385
          have b4e226415 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e226402 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e226402
            | (have j0 := b4e226402 X0 X1
               grind)
            | exact resolve b4e226402 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226402
          have b4e226420 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e226415 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e226415
            | (have j0 := b4e226415 X0 X1
               grind)
            | exact resolve b4e226415 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226415
          have b4e232666 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e226420 y x
               grind)
            | exact superpose b4e226420 b4e20
            | (have j1 := b4e226420 y x
               grind)
            | exact resolve b4e20 b4e226420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e226420
          have b4e236399 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e232666
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e232666
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e232666 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e236405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e232666
               have i₂ := b4e13780 y x
               grind)
            | exact superpose b4e13780 b4e232666
            | (have j1 := b4e13780 y x
               grind)
            | (have r₁ := b4e232666
               have r₂ := b4e13780 y x
               grind)
            | exact resolve b4e232666 b4e13780
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e13780 b4e232666
          have b4e236412 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e236405
          have b4e236413 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e236412
          have b4e236418 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e236399
          have b4e236419 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e236418
          have b4e236427 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e16 y x
               grind)
            | (have r₁ := b4e236413
               have r₂ := b4e16 y x
               grind)
            | exact resolve b4e236413 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e236413
          have b4e237417 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e1049
               have i₂ := b4e236427
               grind)
            | exact superpose b4e236427 b4e1049
            | exact resolve b4e1049 b4e236427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1049
          have b4e237454 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op y y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e121946 y x
               have i₂ := b4e236427
               grind)
            | exact superpose b4e236427 b4e121946
            | (have j0 := b4e121946 y x
               grind)
            | exact resolve b4e121946 b4e236427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121946 b4e236427
          have b4e237477 : (M.op x x) = (k y x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by grind
          clear b4e237417
          have b4e237485 : (τ (M.op y y)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e237454
               have r₂ := b4e26
               grind)
            | exact resolve b4e237454 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e237454
          have b4e238348 : (M.op x y) ≠ (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e151864 y x
               have i₂ := b4e237477
               grind)
            | exact superpose b4e237477 b4e151864
            | (have j0 := b4e151864 y x
               grind)
            | exact resolve b4e151864 b4e237477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e151864
          have b4e238354 : (M.op x y) ≠ (M.op x x) ∨ (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e238348
          have b4e238387 : (τ (M.op x x)) = (M.op (τ x) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have r₁ := b4e238354
               have r₂ := b4e236419
               grind)
            | exact resolve b4e238354 b4e236419
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e236419 b4e238354
          have b4e244926 : (τ (M.op x x)) ≠ (τ (M.op x x)) ∨ (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e240 x (τ y)
               have i₂ := b4e238387
               grind)
            | exact superpose b4e238387 b4e240
            | (have j0 := b4e240 x (τ y)
               grind)
            | (have r₁ := b4e240 x (τ y)
               have r₂ := b4e238387
               grind)
            | exact resolve b4e240 b4e238387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e240 b4e238387
          have b4e244930 : (M.op (τ y) (τ y)) = (k (τ y) (τ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e244926
          have b4e244944 : (τ (k y x)) = (M.op (τ y) (τ y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e244930
               have i₂ := b4e47 x y
               grind)
            | exact superpose b4e47 b4e244930
            | exact resolve b4e244930 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e244930
          have b4e244950 : (τ (M.op y y)) = (τ (k y x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e244944
               have i₂ := b4e182 y
               grind)
            | exact superpose b4e182 b4e244944
            | exact resolve b4e244944 b4e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e182 b4e244944
          have b4e246309 : (τ (M.op x x)) = (τ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ x = y ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e244950
               have i₂ := b4e237477
               grind)
            | exact superpose b4e237477 b4e244950
            | exact resolve b4e244950 b4e237477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e237477 b4e244950
          have b4e246386 : (τ (M.op x x)) = (τ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
          clear b4e246309
          have b4e278045 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e237485
               have i₂ := b4e246386
               grind)
            | exact superpose b4e246386 b4e237485
            | exact resolve b4e237485 b4e246386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e237485 b4e246386
          have b4e278067 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have j1 := b4e17 y x
               grind)
            | (have r₁ := b4e278045
               have r₂ := b4e17 y x
               grind)
            | exact resolve b4e278045 b4e17
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e278045
          have b4e278069 : (τ (M.op x x)) = (τ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have r₁ := b4e278067
               have r₂ := b4e38810
               grind)
            | exact resolve b4e278067 b4e38810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e278067
          have b4e280702 : (M.op x y) = (σ (τ (M.op x x))) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e15 (M.op x y)
               have i₂ := b4e278069
               grind)
            | exact superpose b4e278069 b4e15
            | exact resolve b4e15 b4e278069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e278069
          have b4e280814 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b4e280702
               have i₂ := b4e15 (M.op x x)
               grind)
            | exact superpose b4e15 b4e280702
            | exact resolve b4e280702 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e280702
          have b4e280815 : (M.op x x) = (k y x) ∨ x = y := by
            first
            | (have r₁ := b4e280814
               have r₂ := b4e38810
               grind)
            | exact resolve b4e280814 b4e38810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38810 b4e280814
          have b4e281527 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e2868 x y
               have i₂ := b4e280815
               grind)
            | exact superpose b4e280815 b4e2868
            | (have j0 := b4e2868 x y
               grind)
            | exact resolve b4e2868 b4e280815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2868 b4e280815
          have b4e281551 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b4e281527
          have b4e323772 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ (M.op x x)) = (σ (k y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e281551
               have i₂ := b4e1067
               grind)
            | exact superpose b4e1067 b4e281551
            | exact resolve b4e281551 b4e1067
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1067 b4e281551
          have b4e323796 : (σ (M.op y y)) = (σ (k y x)) ∨ x = y ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have j1 := b4e3091 y x
               grind)
            | (have r₁ := b4e323772
               have r₂ := b4e3091 y x
               grind)
            | exact resolve b4e323772 b4e3091
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3091 b4e323772
          have b4e323800 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b4e323796
               have r₂ := b4e8687
               grind)
            | exact resolve b4e323796 b4e8687
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8687 b4e323796
          have b4e325762 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e323800
               grind)
            | exact superpose b4e323800 b4e20
            | exact resolve b4e20 b4e323800
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323800
          have b4e326190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e325762
               have i₂ := b4e163817
               grind)
            | exact superpose b4e163817 b4e325762
            | exact resolve b4e325762 b4e163817
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e163817 b4e325762
          have b4e326196 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b4e326190
          have b4e326197 : (σ x) = (σ y) ∨ x = y := by grind
          clear b4e326196
          have b4e326605 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e326197
               grind)
            | exact superpose b4e326197 b4e25
            | exact resolve b4e25 b4e326197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e326197
          have b4e326760 : x = y := by grind
          clear b4e326605
          have b4e327261 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e326760
               grind)
            | exact superpose b4e326760 b4e165
            | exact resolve b4e165 b4e326760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165 b4e326760
          have b4e327306 : False := by grind
          exact b4e327306
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b5e22 : (M.op y x) = (M.op x x) := by grind
          have b5e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
               have i₂ := b5e65 (σ X0)
               grind)
            | exact superpose b5e65 b5e19
            | exact resolve b5e19 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e67 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e67
            | exact resolve b5e67 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e67
          have b5e84 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by
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
          have b5e86 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (k x y) := by grind
          clear b5e84
          have b5e87 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e86
               have r₂ := b5e25
               grind)
            | exact resolve b5e86 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e86
          have b5e103 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e143 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e76 y
               grind)
            | exact superpose b5e76 b5e23
            | exact resolve b5e23 b5e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e1400 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e103 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e1401 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1400
               have r₂ := b5e24
               grind)
            | exact resolve b5e1400 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1400
          have b5e1407 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1401
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1401
            | exact resolve b5e1401 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1401
          have b5e1411 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1407
               have i₂ := b5e87
               grind)
            | exact superpose b5e87 b5e1407
            | exact resolve b5e1407 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87 b5e1407
          have b5e1412 : False := by grind
          exact b5e1412
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e21 : (M.op y x) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e50 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
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
        have b6e71 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e74 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b6e71
        have b6e77 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e74
          | exact resolve b6e74 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e78 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e51 x
             grind)
          | exact superpose b6e51 b6e77
          | exact resolve b6e77 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e77
        have b6e133 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e78
             grind)
          | exact superpose b6e78 b6e13
          | exact resolve b6e13 b6e78
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e134 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b6e133
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e133
          | exact resolve b6e133 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e133
        have b6e152 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e134
             grind)
          | exact superpose b6e134 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e153 : (M.op y x) = (M.op x x) ∨ (M.op y x) = (M.op y y) := by grind
        clear b6e152
        have b6e155 : (M.op y x) = (M.op y y) := by
          first
          | (have r₁ := b6e153
             have r₂ := b6e21
             grind)
          | exact resolve b6e153 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e157 : False := by grind
        exact b6e157
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e22 : (M.op y x) ≠ (M.op x x) := by grind
          have b7e23 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by grind
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
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e65 (σ X0)
               grind)
            | exact superpose b7e65 b7e19
            | exact resolve b7e19 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e67 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e67
          have b7e84 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e86 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e84
          have b7e87 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e25
               grind)
            | exact resolve b7e86 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e86
          have b7e88 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e87
            | exact resolve b7e87 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e89 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e88
               have i₂ := b7e76 y
               grind)
            | exact superpose b7e76 b7e88
            | exact resolve b7e88 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e88
          have b7e94 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e14
            | exact resolve b7e14 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e95 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e152 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e95
               grind)
            | exact superpose b7e95 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e153 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op x x) := by grind
          clear b7e152
          have b7e155 : (M.op y x) = (M.op x x) := by
            first
            | (have r₁ := b7e153
               have r₂ := b7e21
               grind)
            | exact resolve b7e153 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153
          have b7e157 : False := by grind
          exact b7e157
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b8e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e62 (σ X0)
               grind)
            | exact superpose b8e62 b8e19
            | exact resolve b8e19 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e67 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e62 (τ X0)
               grind)
            | exact superpose b8e62 b8e26
            | exact resolve b8e26 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e67 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e67
            | exact resolve b8e67 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e64 X0
               have i₂ := b8e62 X0
               grind)
            | exact superpose b8e62 b8e64
            | exact resolve b8e64 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e76 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e70 X0
               have i₂ := b8e62 X0
               grind)
            | exact superpose b8e62 b8e70
            | exact resolve b8e70 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62 b8e70
          have b8e90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (σ X0)
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e16
            | (have j0 := b8e16 X1 (σ X0)
               grind)
            | exact resolve b8e16 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e125 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e131 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e113 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e135 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e138 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e125 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e125
            | (have j0 := b8e125 X0 X1
               grind)
            | exact resolve b8e125 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125
          have b8e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               have j1 := b8e131 X1 X0
               grind)
            | (have r₁ := b8e133 X0 X1
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X1 X0
               have r₂ := b8e131 X0 X1
               grind)
            | (have r₁ := b8e133 X0 X0
               have r₂ := b8e131 X0 X0
               grind)
            | exact resolve b8e133 b8e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131 b8e133
          have b8e143 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e138 X0 X1
               have i₂ := b8e73 X1
               grind)
            | exact superpose b8e73 b8e138
            | (have j0 := b8e138 X0 X1
               grind)
            | exact resolve b8e138 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e149 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e76 X0
               have i₂ := b8e18 X1 (τ X0)
               grind)
            | (have i₁ := b8e76 X0
               have i₂ := b8e18 (τ X0) (τ X0)
               grind)
            | exact superpose b8e18 b8e76
            | (have j1 := b8e18 X1 (τ X0)
               grind)
            | exact resolve b8e76 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e155 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e14
            | exact resolve b8e14 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e252 : ∀ X0 X1 : G, (M.op (τ X0) X1) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 (τ X0)
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e16
            | (have j0 := b8e16 X1 (τ X0)
               grind)
            | exact resolve b8e16 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e338 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X0 X0) = (M.op (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1 X0
               have i₂ := b8e135 (τ X1) X0
               grind)
            | exact superpose b8e135 b8e26
            | (have j1 := b8e135 (τ X1) X0
               grind)
            | exact resolve b8e26 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e344 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e135 (τ X0) X1
               grind)
            | exact superpose b8e135 b8e26
            | (have j1 := b8e135 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e460 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e140 X1 (τ X0)
               grind)
            | exact superpose b8e140 b8e26
            | (have j1 := b8e140 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e140
          have b8e480 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op (τ X0) (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e460 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e460
            | (have j0 := b8e460 X0 X1
               grind)
            | exact resolve b8e460 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e499 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e480 X0 X1
               have i₂ := b8e155 X0
               grind)
            | exact superpose b8e155 b8e480
            | (have j0 := b8e480 X0 X1
               grind)
            | exact resolve b8e480 b8e155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e155 b8e480
          have b8e2049 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e143 X1 X0
               grind)
            | exact superpose b8e143 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e143 X1 X0
               grind)
            | exact resolve b8e16 b8e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2072 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2073 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2074 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e2135 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e2049 X0 X1
               have j1 := b8e90 X1 (σ X0)
               grind)
            | (have r₁ := b8e2049 X0 X0
               have r₂ := b8e90 X0 (σ X0)
               grind)
            | (have r₁ := b8e2049 X0 X0
               have r₂ := b8e90 X0 (σ X0)
               grind)
            | exact resolve b8e2049 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90 b8e2049
          have b8e2204 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2135 X0 X1
               have i₂ := b8e73 X1
               grind)
            | exact superpose b8e73 b8e2135
            | (have j0 := b8e2135 X0 X1
               grind)
            | exact resolve b8e2135 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2135
          have b8e2253 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2204 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e2204
            | (have j0 := b8e2204 X0 X1
               grind)
            | exact resolve b8e2204 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2204
          have b8e2284 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e2253 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e2253
            | (have j0 := b8e2253 X0 X1
               grind)
            | exact resolve b8e2253 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2253
          have b8e6462 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e344 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e344
            | exact resolve b8e344 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e344
          have b8e6671 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e6462 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e6462
            | (have j0 := b8e6462 X0 X1
               grind)
            | exact resolve b8e6462 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6462
          have b8e8534 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e252 X0 X1
               have i₂ := b8e499 X0 X1
               grind)
            | exact superpose b8e499 b8e252
            | (have j0 := b8e252 X0 X1
               have j1 := b8e499 X0 X1
               grind)
            | (have r₁ := b8e252 X0 X1
               have r₂ := b8e499 X0 X1
               grind)
            | exact resolve b8e252 b8e499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252 b8e499
          have b8e8729 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have j0 := b8e8534 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8534
          have b8e13755 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2284 (τ X1) (τ X0)
               have i₂ := b8e41 X0 X1
               grind)
            | exact superpose b8e41 b8e2284
            | (have j0 := b8e2284 (τ X0) (τ X1)
               grind)
            | exact resolve b8e2284 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2284
          have b8e13843 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13755 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13755
            | (have j0 := b8e13755 X0 X1
               grind)
            | exact resolve b8e13755 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13755
          have b8e13874 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13843 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e13843
            | (have j0 := b8e13843 X0 X1
               grind)
            | exact resolve b8e13843 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13843
          have b8e13899 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13874 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e13874
            | (have j0 := b8e13874 X0 X1
               grind)
            | exact resolve b8e13874 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13874
          have b8e13914 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13899 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e13899
            | (have j0 := b8e13899 X0 X1
               grind)
            | exact resolve b8e13899 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13899
          have b8e13923 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13914 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e13914
            | (have j0 := b8e13914 X0 X1
               grind)
            | exact resolve b8e13914 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13914
          have b8e13927 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13923 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e13923
            | (have j0 := b8e13923 X0 X1
               grind)
            | exact resolve b8e13923 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13923
          have b8e13928 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13927 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e13927
            | (have j0 := b8e13927 X0 X1
               grind)
            | exact resolve b8e13927 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13927
          have b8e23827 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2073 (τ X1) (τ X0)
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e2073
            | (have j0 := b8e2073 (τ X1) (τ X0)
               grind)
            | exact resolve b8e2073 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2073
          have b8e23939 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23827 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e23827
            | (have j0 := b8e23827 X0 X1
               grind)
            | exact resolve b8e23827 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23827
          have b8e23985 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23939 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e23939
            | (have j0 := b8e23939 X0 X1
               grind)
            | exact resolve b8e23939 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23939
          have b8e24023 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e23985 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e23985
            | (have j0 := b8e23985 X0 X1
               grind)
            | exact resolve b8e23985 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23985
          have b8e24053 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24023 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e24023
            | (have j0 := b8e24023 X0 X1
               grind)
            | exact resolve b8e24023 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24023
          have b8e24079 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24053 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e24053
            | (have j0 := b8e24053 X0 X1
               grind)
            | exact resolve b8e24053 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24053
          have b8e24101 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e24079 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e24079
            | (have j0 := b8e24079 X0 X1
               grind)
            | exact resolve b8e24079 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24079
          have b8e24118 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e24101 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e24101
            | (have j0 := b8e24101 X0 X1
               grind)
            | exact resolve b8e24101 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24101
          have b8e24131 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e24118 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e24118
            | (have j0 := b8e24118 X0 X1
               grind)
            | exact resolve b8e24118 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24118
          have b8e24620 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e2074 (τ X1) (τ X0)
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e2074
            | (have j0 := b8e2074 (τ X1) (τ X0)
               grind)
            | exact resolve b8e2074 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2074
          have b8e24732 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24620 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e24620
            | (have j0 := b8e24620 X0 X1
               grind)
            | exact resolve b8e24620 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24620
          have b8e24780 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24732 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e24732
            | (have j0 := b8e24732 X0 X1
               grind)
            | exact resolve b8e24732 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24732
          have b8e24815 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24780 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e24780
            | (have j0 := b8e24780 X0 X1
               grind)
            | exact resolve b8e24780 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24780
          have b8e24842 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24815 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e24815
            | (have j0 := b8e24815 X0 X1
               grind)
            | exact resolve b8e24815 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24815
          have b8e24865 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e24842 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e24842
            | (have j0 := b8e24842 X0 X1
               grind)
            | exact resolve b8e24842 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24842
          have b8e24887 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e24865 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e24865
            | (have j0 := b8e24865 X0 X1
               grind)
            | exact resolve b8e24865 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24865
          have b8e24904 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e24887 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e24887
            | (have j0 := b8e24887 X0 X1
               grind)
            | exact resolve b8e24887 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24887
          have b8e24917 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e24904 X0 X1
               have i₂ := b8e76 X1
               grind)
            | exact superpose b8e76 b8e24904
            | (have j0 := b8e24904 X0 X1
               grind)
            | exact resolve b8e24904 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24904
          have b8e91428 : ∀ X0 X1 : G, (k X0 (σ (τ X1))) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 (τ X1)
               have i₂ := b8e8729 X1 (τ X0)
               grind)
            | exact superpose b8e8729 b8e25
            | (have j1 := b8e8729 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e8729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e91863 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e8729 (σ X0) X1
               grind)
            | exact superpose b8e8729 b8e30
            | (have j1 := b8e8729 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e8729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8729
          have b8e92113 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e91863 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e91863
            | (have j0 := b8e91863 X0 X1
               grind)
            | exact resolve b8e91863 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91863
          have b8e92287 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ (τ X1))) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e91428 X0 X1
               have i₂ := b8e76 X0
               grind)
            | exact superpose b8e76 b8e91428
            | (have j0 := b8e91428 X0 X1
               grind)
            | exact resolve b8e91428 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e91428
          have b8e92566 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92113 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e92113
            | (have j0 := b8e92113 X0 X1
               grind)
            | exact resolve b8e92113 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92113
          have b8e92652 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (σ (τ X0)) X1) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e92287 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e92287
            | (have j0 := b8e92287 X0 X1
               grind)
            | exact resolve b8e92287 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92287
          have b8e92815 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92566 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e92566
            | (have j0 := b8e92566 X0 X1
               grind)
            | exact resolve b8e92566 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92566
          have b8e92880 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e92652 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e92652
            | (have j0 := b8e92652 X0 X1
               grind)
            | exact resolve b8e92652 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92652
          have b8e92981 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e92815 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e92815
            | (have j0 := b8e92815 X0 X1
               grind)
            | exact resolve b8e92815 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92815
          have b8e93033 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e92880 X0 X1
               have i₂ := b8e41 X1 X0
               grind)
            | exact superpose b8e41 b8e92880
            | (have j0 := b8e92880 X0 X1
               grind)
            | exact resolve b8e92880 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e92880
          have b8e93081 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e92981 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e92981
            | (have j0 := b8e92981 X0 X1
               grind)
            | exact resolve b8e92981 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92981
          have b8e94675 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e93081 (σ X0) X1
               grind)
            | exact superpose b8e93081 b8e30
            | (have j1 := b8e93081 (σ X0) X1
               grind)
            | exact resolve b8e30 b8e93081
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93081
          have b8e95175 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e94675 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e94675
            | (have j0 := b8e94675 X0 X1
               grind)
            | exact resolve b8e94675 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e94675
          have b8e95808 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e95175 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e95175
            | (have j0 := b8e95175 X0 X1
               grind)
            | exact resolve b8e95175 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95175
          have b8e106142 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13928 X0 X1
               have i₂ := b8e93033 X0 X1
               grind)
            | exact superpose b8e93033 b8e13928
            | (have j0 := b8e13928 X1 X0
               have j1 := b8e93033 X1 X0
               grind)
            | (have r₁ := b8e13928 X0 X1
               have r₂ := b8e93033 X0 X1
               grind)
            | (have r₁ := b8e13928 X1 X1
               have r₂ := b8e93033 X1 X1
               grind)
            | exact resolve b8e13928 b8e93033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106410 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e24131 X0 X1
               have i₂ := b8e93033 X0 X1
               grind)
            | exact superpose b8e93033 b8e24131
            | (have j0 := b8e24131 X0 X1
               have j1 := b8e93033 X0 X1
               grind)
            | (have r₁ := b8e24131 X1 X1
               have r₂ := b8e93033 X1 X1
               grind)
            | (have r₁ := b8e24131 X0 X1
               have r₂ := b8e93033 X0 X1
               grind)
            | exact resolve b8e24131 b8e93033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24131
          have b8e106896 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e93033 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106897 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e93033 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93033
          have b8e106930 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e106410 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106410
          have b8e106968 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e106142 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106142
          have b8e107576 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e106930 X0 X1
               have j1 := b8e24917 X0 X1
               grind)
            | (have r₁ := b8e106930 X0 X1
               have r₂ := b8e24917 X0 X1
               grind)
            | exact resolve b8e106930 b8e24917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24917 b8e106930
          have b8e107790 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e106968 X0 X1
               have j1 := b8e106896 X1 X0
               grind)
            | (have r₁ := b8e106968 X0 X1
               have r₂ := b8e106896 X0 X1
               grind)
            | (have r₁ := b8e106968 X1 X0
               have r₂ := b8e106896 X0 X1
               grind)
            | (have r₁ := b8e106968 X0 X0
               have r₂ := b8e106896 X0 X0
               grind)
            | exact resolve b8e106968 b8e106896
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106896 b8e106968
          have b8e135483 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e107576 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e107576 X0 X1
               grind)
            | exact superpose b8e107576 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e107576 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e107576 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e107576 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e107576 X0 X0
               grind)
            | exact resolve b8e17 b8e107576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e136674 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e107576 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107576
          have b8e136745 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e135483 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135483
          have b8e137052 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e136745 X0 X1
               have j1 := b8e106897 X0 X1
               grind)
            | (have r₁ := b8e136745 X0 X1
               have r₂ := b8e106897 X0 X1
               grind)
            | (have r₁ := b8e136745 X1 X0
               have r₂ := b8e106897 X0 X1
               grind)
            | (have r₁ := b8e136745 X0 X0
               have r₂ := b8e106897 X0 X0
               grind)
            | exact resolve b8e136745 b8e106897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106897 b8e136745
          have b8e142616 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e107790 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e107790
            | (have j0 := b8e107790 (σ X0) X1
               grind)
            | exact resolve b8e107790 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107790
          have b8e144293 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e142616 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e142616
            | (have j0 := b8e142616 X0 X1
               grind)
            | exact resolve b8e142616 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e142616
          have b8e165628 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e136674 X1 (σ X0)
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e136674
            | (have j0 := b8e136674 X1 (σ X0)
               grind)
            | exact resolve b8e136674 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136674
          have b8e165738 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e165628 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e165628
            | (have j0 := b8e165628 X0 X1
               grind)
            | exact resolve b8e165628 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165628
          have b8e165742 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e165738 X0 X1
               have i₂ := b8e38 X0 X1
               grind)
            | exact superpose b8e38 b8e165738
            | (have j0 := b8e165738 X0 X1
               grind)
            | exact resolve b8e165738 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165738
          have b8e170154 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ (k (σ X1) X0)) = (M.op (τ X0) (τ (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e338 X1 X0
               have i₂ := b8e137052 (σ X1) X0
               grind)
            | exact superpose b8e137052 b8e338
            | (have j0 := b8e338 X1 X0
               have j1 := b8e137052 (σ X1) X0
               grind)
            | exact resolve b8e338 b8e137052
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338 b8e137052
          have b8e170541 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ (k (σ X1) X0)) = (M.op (τ X0) (τ (σ X1))) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e170154 X0 X1
               have j1 := b8e165742 X1 X0
               grind)
            | (have r₁ := b8e170154 X1 X0
               have r₂ := b8e165742 X0 X1
               grind)
            | exact resolve b8e170154 b8e165742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165742 b8e170154
          have b8e170988 : ∀ X0 X1 : G, (τ (k (σ X1) X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e170541 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e170541
            | (have j0 := b8e170541 X0 X1
               grind)
            | exact resolve b8e170541 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170541
          have b8e171311 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e170988 X0 X1
               have i₂ := b8e38 X1 X0
               grind)
            | exact superpose b8e38 b8e170988
            | (have j0 := b8e170988 X0 X1
               grind)
            | exact resolve b8e170988 b8e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170988
          have b8e171312 : ∀ X0 X1 : G, (k X1 (τ X0)) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e171311 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171311
          have b8e209910 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e95808 X1 (σ X0)
               grind)
            | exact superpose b8e95808 b8e38
            | (have j1 := b8e95808 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e95808
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e95808
          have b8e209974 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209910 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e209910
            | (have j0 := b8e209910 X0 X1
               grind)
            | exact resolve b8e209910 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209910
          have b8e210003 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e209974 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e209974
            | (have j0 := b8e209974 X0 X1
               grind)
            | exact resolve b8e209974 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e209974
          have b8e210020 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e210003 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e210003
            | (have j0 := b8e210003 X0 X1
               grind)
            | exact resolve b8e210003 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210003
          have b8e210033 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e210020 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e210020
            | (have j0 := b8e210020 X0 X1
               grind)
            | exact resolve b8e210020 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210020
          have b8e210038 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e210033 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e210033
            | (have j0 := b8e210033 X0 X1
               grind)
            | exact resolve b8e210033 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210033
          have b8e217523 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e210038 y x
               grind)
            | exact superpose b8e210038 b8e20
            | (have j1 := b8e210038 y x
               grind)
            | exact resolve b8e20 b8e210038
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e210038
          have b8e218081 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e217523
               have i₂ := b8e6671 x y
               grind)
            | exact superpose b8e6671 b8e217523
            | (have j1 := b8e6671 x y
               grind)
            | (have r₁ := b8e217523
               have r₂ := b8e6671 x y
               grind)
            | exact resolve b8e217523 b8e6671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6671 b8e217523
          have b8e218092 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e218081
          have b8e218093 : (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e218092
          have b8e218100 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have j1 := b8e13928 y x
               grind)
            | (have r₁ := b8e218093
               have r₂ := b8e13928 y x
               grind)
            | exact resolve b8e218093 b8e13928
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13928 b8e218093
          have b8e276902 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e38 X0 (σ X1)
               have i₂ := b8e144293 X1 (σ X0)
               grind)
            | exact superpose b8e144293 b8e38
            | (have j1 := b8e144293 X1 (σ X0)
               grind)
            | exact resolve b8e38 b8e144293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38 b8e144293
          have b8e276907 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e276902 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e276902
            | (have j0 := b8e276902 X0 X1
               grind)
            | exact resolve b8e276902 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276902
          have b8e276925 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e276907 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e276907
            | (have j0 := b8e276907 X0 X1
               grind)
            | exact resolve b8e276907 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276907
          have b8e276936 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e276925 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e276925
            | (have j0 := b8e276925 X0 X1
               grind)
            | exact resolve b8e276925 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276925
          have b8e276942 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e276936 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e276936
            | (have j0 := b8e276936 X0 X1
               grind)
            | exact resolve b8e276936 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276936
          have b8e276943 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e276942 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e276942
            | (have j0 := b8e276942 X0 X1
               grind)
            | exact resolve b8e276942 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276942
          have b8e284614 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e276943 y x
               grind)
            | exact superpose b8e276943 b8e20
            | (have j1 := b8e276943 y x
               grind)
            | exact resolve b8e20 b8e276943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e276943
          have b8e322049 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e171312 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e171312
            | (have j0 := b8e171312 (σ X0) X1
               grind)
            | exact resolve b8e171312 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171312
          have b8e322131 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e322049 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e322049
            | (have j0 := b8e322049 X0 X1
               grind)
            | exact resolve b8e322049 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322049
          have b8e327955 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e322131 x y
               grind)
            | exact superpose b8e322131 b8e20
            | (have j1 := b8e322131 x y
               grind)
            | exact resolve b8e20 b8e322131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322131
          have b8e400836 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e149 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e149
            | exact resolve b8e149 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149
          have b8e400902 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e400836 X0 X1
               have i₂ := b8e73 X0
               grind)
            | exact superpose b8e73 b8e400836
            | (have j0 := b8e400836 X0 X1
               grind)
            | exact resolve b8e400836 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73 b8e400836
          have b8e402781 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e327955
               have i₂ := b8e400902 x y
               grind)
            | exact superpose b8e400902 b8e327955
            | (have j1 := b8e400902 x y
               grind)
            | (have r₁ := b8e327955
               have r₂ := b8e400902 x y
               grind)
            | exact resolve b8e327955 b8e400902
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e327955 b8e400902
          have b8e402874 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
          clear b8e402781
          have b8e402875 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e402874
          have b8e407272 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e218100
               have i₂ := b8e402875
               grind)
            | exact superpose b8e402875 b8e218100
            | exact resolve b8e218100 b8e402875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e218100 b8e402875
          have b8e407308 : (M.op x y) = (M.op y y) := by grind
          clear b8e407272
          have b8e411319 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b8e284614
               have i₂ := b8e407308
               grind)
            | exact superpose b8e407308 b8e284614
            | exact resolve b8e284614 b8e407308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e284614
          have b8e411323 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b8e17 y X0
               have i₂ := b8e407308
               grind)
            | exact superpose b8e407308 b8e17
            | (have j0 := b8e17 y X0
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e407308
               grind)
            | exact resolve b8e17 b8e407308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e411581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) := by grind
          clear b8e411319
          have b8e411582 : (M.op x y) = (k y x) := by grind
          clear b8e411581
          have b8e420612 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e2072 x y
               have i₂ := b8e411582
               grind)
            | exact superpose b8e411582 b8e2072
            | (have j0 := b8e2072 x y
               grind)
            | exact resolve b8e2072 b8e411582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2072
          have b8e420648 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e420612
               have r₂ := b8e20
               grind)
            | exact resolve b8e420612 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e420612
          have b8e420658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e420648
               have i₂ := b8e407308
               grind)
            | exact superpose b8e407308 b8e420648
            | exact resolve b8e420648 b8e407308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e407308 b8e420648
          have b8e420665 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have r₁ := b8e420658
               have r₂ := b8e20
               grind)
            | exact resolve b8e420658 b8e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e420658
          have b8e467321 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j0 := b8e411323 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e411323
          have b8e467322 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e467321
               have i₂ := b8e411582
               grind)
            | exact superpose b8e411582 b8e467321
            | exact resolve b8e467321 b8e411582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e411582 b8e467321
          have b8e467323 : (M.op x y) = (M.op x x) := by grind
          clear b8e467322
          have b8e467691 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e420665
               have i₂ := b8e467323
               grind)
            | exact superpose b8e467323 b8e420665
            | exact resolve b8e420665 b8e467323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e420665 b8e467323
          have b8e467761 : False := by grind
          exact b8e467761
