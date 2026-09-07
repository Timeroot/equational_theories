import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation647`: `x = x ◇ (y ◇ ((y ◇ z) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pyx_Equation647 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law647 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law647.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e78 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e83 : False := by grind
      exact b0e83
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
               have i₂ := b4e13 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b4e35 X0 x x X3
               have i₂ := b4e13 X0 x x
               grind)
            | exact superpose b4e13 b4e35
            | exact resolve b4e35 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e64 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X1) (M.op (σ X1) (σ X1))
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e64 X0 X1
               have i₂ := b4e30 X1
               grind)
            | exact superpose b4e30 b4e64
            | (have j0 := b4e64 X0 X1
               grind)
            | exact resolve b4e64 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e114 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e36 (σ X0) X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e36
            | exact resolve b4e36 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e190 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e70 x y
               grind)
            | exact superpose b4e70 b4e20
            | (have j1 := b4e70 (M.op y y) y
               grind)
            | exact resolve b4e20 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e204 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e190
               have r₂ := b4e23
               grind)
            | exact resolve b4e190 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e190
          have b4e1242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e204
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e204
            | (have j1 := b4e18 y (M.op y y)
               grind)
            | (have r₁ := b4e204
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e204
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e204 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e204
          have b4e1243 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b4e1242
          have b4e1246 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b4e1243
               have r₂ := b4e21
               grind)
            | exact resolve b4e1243 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1243
          have b4e3687 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e1246
               grind)
            | exact superpose b4e1246 b4e14
            | exact resolve b4e14 b4e1246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1246
          have b4e3734 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e3687
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e3687
            | exact resolve b4e3687 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3687
          have b4e3735 : y = (M.op y y) := by grind
          clear b4e3734
          have b4e3922 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e36 y X0
               have i₂ := b4e3735
               grind)
            | exact superpose b4e3735 b4e36
            | exact resolve b4e36 b4e3735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e3925 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e114 y X0
               have i₂ := b4e3735
               grind)
            | exact superpose b4e3735 b4e114
            | exact resolve b4e114 b4e3735
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114 b4e3735
          have b4e4406 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e3925 (σ x)
               grind)
            | exact superpose b4e3925 b4e20
            | exact resolve b4e20 b4e3925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3925
          have b4e4411 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e4406
               have i₂ := b4e3922 x
               grind)
            | exact superpose b4e3922 b4e4406
            | exact resolve b4e4406 b4e3922
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3922 b4e4406
          have b4e4412 : False := by grind
          exact b4e4412
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e98 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e103 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e98
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e98
            | exact resolve b5e98 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e98
          have b5e104 : False := by grind
          exact b5e104
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
               have i₂ := b7e13 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b7e34 X0 x x X3
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e34
            | exact resolve b7e34 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e38 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b7e35 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e94 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e38 (σ x)
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e38
            | exact resolve b7e38 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e38
          have b7e109 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e14
            | exact resolve b7e14 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e110 : x = (M.op x x) := by
            first
            | (have i₁ := b7e109
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e109
            | exact resolve b7e109 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e109
          have b7e114 : False := by grind
          exact b7e114
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X3 X0 (M.op X1 (M.op (M.op X1 X2) X2))
               have i₂ := b8e13 (M.op X0 (M.op X1 (M.op (M.op X1 X2) X2))) X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X0)) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b8e33 X0 x x X3
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (M.op (σ X1) (σ X1))
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e54 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e54
            | (have j0 := b8e54 X0 X1
               grind)
            | exact resolve b8e54 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e85 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e34 (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e34
            | exact resolve b8e34 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e153 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e20
            | (have j1 := b8e63 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e167 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e153
               have r₂ := b8e23
               grind)
            | exact resolve b8e153 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153
          have b8e1162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e167
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e167
            | (have j1 := b8e18 y (M.op y y)
               grind)
            | (have r₁ := b8e167
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e167
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e167 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167
          have b8e1163 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = y := by grind
          clear b8e1162
          have b8e1166 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
            first
            | (have r₁ := b8e1163
               have r₂ := b8e21
               grind)
            | exact resolve b8e1163 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1163
          have b8e1175 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e1166
               grind)
            | exact superpose b8e1166 b8e14
            | exact resolve b8e14 b8e1166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1166
          have b8e1209 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1175
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e1175
            | exact resolve b8e1175 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1175
          have b8e1210 : y = (M.op y y) := by grind
          clear b8e1209
          have b8e1243 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e34 y X0
               have i₂ := b8e1210
               grind)
            | exact superpose b8e1210 b8e34
            | exact resolve b8e34 b8e1210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e1246 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e85 y X0
               have i₂ := b8e1210
               grind)
            | exact superpose b8e1210 b8e85
            | exact resolve b8e85 b8e1210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85 b8e1210
          have b8e1458 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1246 (σ x)
               grind)
            | exact superpose b8e1246 b8e20
            | exact resolve b8e20 b8e1246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1246
          have b8e1466 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e1458
               have i₂ := b8e1243 x
               grind)
            | exact superpose b8e1243 b8e1458
            | exact resolve b8e1458 b8e1243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1243 b8e1458
          have b8e1467 : False := by grind
          exact b8e1467

/-- `Equation690`: `x = y ◇ (x ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation690 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law690 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law690.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e28 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X1 X3
           have i₂ := b0e11 X0 (M.op X3 X1) X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : x = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e28 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e28
        | exact resolve b0e28 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 y) X0)) = (M.op x (M.op (M.op X0 (M.op (M.op X1 y) X0)) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (M.op X0 (M.op (M.op X1 y) X0))
           have i₂ := b0e11 X0 y X1
           grind)
        | exact superpose b0e11 b0e28
        | exact resolve b0e28 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e53 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (M.op x y) x
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (σ x) (M.op (M.op X0 (M.op (M.op X1 (σ y)) X0)) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e29 (M.op X0 (M.op (M.op X1 (σ y)) X0))
           have i₂ := b0e11 X0 (σ y) X1
           grind)
        | exact superpose b0e11 b0e29
        | exact resolve b0e29 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X4 X5) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e30 (M.op X1 (M.op (M.op X2 X3) X1)) X4 X5 (M.op X0 (M.op X1 X0))
           have i₂ := b0e30 X1 X2 X3 X0
           grind)
        | exact superpose b0e30 b0e30
        | exact resolve b0e30 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e128 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
           have i₂ := b0e30 X1 x x X0
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e266 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (M.op X1 (M.op X0 X1)) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 X0 (M.op (σ y) X0) (σ x) X0
           have i₂ := b0e29 X0
           grind)
        | exact superpose b0e29 b0e31
        | exact resolve b0e31 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e282 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X1 (M.op X2 X0)) X0) X0
           have i₂ := b0e31 X0 X0 X1 X2
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e285 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e30 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3 X4 X0
           have i₂ := b0e31 X0 X0 X1 X2
           grind)
        | exact superpose b0e31 b0e30
        | exact resolve b0e30 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e289 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) = (M.op (M.op X3 (M.op (M.op X4 X5) X3)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e30 X3 X4 X5 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)
           have i₂ := b0e31 X0 X3 X1 X2
           grind)
        | exact superpose b0e31 b0e30
        | exact resolve b0e30 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e380 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X1) (σ X0)
           have i₂ := b0e46 X1 X0
           grind)
        | exact superpose b0e46 b0e14
        | (have j0 := b0e14 (σ X1) (σ X0)
           have j1 := b0e46 X1 X0
           grind)
        | (have r₁ := b0e14 (σ X1) (σ X1)
           have r₂ := b0e46 X1 X1
           grind)
        | (have r₁ := b0e14 (σ X0) (σ X1)
           have r₂ := b0e46 X0 X1
           grind)
        | exact resolve b0e14 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e390 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e380 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e380
      have b0e402 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e390 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e390
        | (have j0 := b0e390 X0 X1
           grind)
        | exact resolve b0e390 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e390
      have b0e669 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 y)) y) := by
        intro X0
        first
        | (have i₁ := b0e128 y X0 (M.op x y)
           have i₂ := b0e53 y
           grind)
        | exact superpose b0e53 b0e128
        | exact resolve b0e128 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1581 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op y (M.op (M.op X0 y) y)) := by
        intro X0
        first
        | (have i₁ := b0e33 y X0
           have i₂ := b0e669 (M.op X0 y)
           grind)
        | exact superpose b0e669 b0e33
        | exact resolve b0e33 b0e669
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e669
      have b0e1615 : ∀ X0 : G, x = (M.op y (M.op (M.op X0 y) y)) := by
        intro X0
        first
        | (have i₁ := b0e1581 X0
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e1581
        | exact resolve b0e1581 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1581
      have b0e2250 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) X1 X0
           have i₂ := b0e282 (M.op X0 X1) X2 X3
           grind)
        | exact superpose b0e282 b0e11
        | exact resolve b0e11 b0e282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e9904 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e402 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e402
      have b0e9906 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e9904 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9904
      have b0e28332 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e31 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X5 X3 X4
           have i₂ := b0e285 X0 X1 X2 X3 (M.op X4 X5)
           grind)
        | exact superpose b0e285 b0e31
        | exact resolve b0e31 b0e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28333 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (σ y)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e84 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3
           have i₂ := b0e285 X0 X1 X2 X3 (σ y)
           grind)
        | exact superpose b0e285 b0e84
        | exact resolve b0e84 b0e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84
      have b0e28343 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) = (M.op (M.op (σ y) (M.op X3 X4)) X0) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e266 (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))
           have i₂ := b0e285 X0 X1 X2 X3 X4
           grind)
        | exact superpose b0e285 b0e266
        | exact resolve b0e266 b0e285
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e266 b0e285
      have b0e28461 : ∀ X0 X3 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op X3 (σ y))) X0) := by
        intro X0 X3
        first
        | (have i₁ := b0e28333 X0 x x X3
           have i₂ := b0e28343 X0 x x X3 (σ y)
           grind)
        | exact superpose b0e28343 b0e28333
        | exact resolve b0e28333 b0e28343
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28333
      have b0e28462 : ∀ X0 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op (σ y) (M.op X3 (M.op X4 X5))) X0) := by
        intro X0 X3 X4 X5
        first
        | (have i₁ := b0e28332 X0 x x X3 X4 X5
           have i₂ := b0e28343 X0 x x X3 (M.op X4 X5)
           grind)
        | exact superpose b0e28343 b0e28332
        | exact resolve b0e28332 b0e28343
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28332 b0e28343
      have b0e37360 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X0)) X1) = (M.op (M.op (σ y) (M.op X2 X0)) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e28462 X1 X2 x (M.op X0 (M.op y X0))
           have i₂ := b0e28 X0
           grind)
        | exact superpose b0e28 b0e28462
        | exact resolve b0e28462 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37409 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (σ y) X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e28462 X2 (M.op X1 (M.op x X1)) X0 (M.op X1 X0)
           have i₂ := b0e128 X1 x X0
           grind)
        | exact superpose b0e128 b0e28462
        | exact resolve b0e28462 b0e128
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37424 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e28462 X1 (M.op x y) X0 (M.op x X0)
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e28462
        | exact resolve b0e28462 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e37472 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e28462 X1 x X0 (M.op y X0)
           have i₂ := b0e28 X0
           grind)
        | exact superpose b0e28 b0e28462
        | exact resolve b0e28462 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e37481 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (σ y) x) X0) := by
        intro X0
        first
        | (have i₁ := b0e28462 X0 y (M.op x y) y
           have i₂ := b0e1615 x
           grind)
        | exact superpose b0e1615 b0e28462
        | exact resolve b0e28462 b0e1615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1615
      have b0e37885 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e37424 X0 X1
           have i₂ := b0e37472 X0 X1
           grind)
        | exact superpose b0e37472 b0e37424
        | exact resolve b0e37424 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37424
      have b0e37921 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X0)) X1) = (M.op (M.op y (M.op X2 X0)) X1) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e37360 X0 X1 X2
           have i₂ := b0e37472 (M.op X2 X0) X1
           grind)
        | exact superpose b0e37472 b0e37360
        | exact resolve b0e37360 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37360
      have b0e53956 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e37409 X1 X0 X2
           have i₂ := b0e37409 X1 X3 X2
           grind)
        | (have i₁ := b0e37409 X0 X1 X2
           have i₂ := b0e37409 X0 (σ y) X2
           grind)
        | exact superpose b0e37409 b0e37409
        | exact resolve b0e37409 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e54263 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X3 X1)) (M.op (M.op (σ y) X0) (M.op X1 (M.op X2 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e128 X1 X3 (M.op X2 X0)
           have i₂ := b0e37409 X0 X2 (M.op X1 (M.op X2 X0))
           grind)
        | (have i₁ := b0e128 X0 X1 (M.op (σ y) X0)
           have i₂ := b0e37409 X0 X1 (M.op X0 (M.op (σ y) X0))
           grind)
        | exact superpose b0e37409 b0e128
        | exact resolve b0e128 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128
      have b0e54406 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e37481 X1
           have i₂ := b0e37409 x X0 X1
           grind)
        | (have i₁ := b0e37481 x
           have i₂ := b0e37409 x (σ y) x
           grind)
        | exact superpose b0e37409 b0e37481
        | exact resolve b0e37481 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37481
      have b0e54408 : ∀ X0 X1 X2 : G, (M.op (σ x) X2) = (M.op (M.op X0 (M.op X1 (σ y))) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e28461 X2 X1
           have i₂ := b0e37409 (M.op X1 (σ y)) X0 X2
           grind)
        | (have i₁ := b0e28461 X2 x
           have i₂ := b0e37409 (M.op x (σ y)) (σ y) X2
           grind)
        | exact superpose b0e37409 b0e28461
        | exact resolve b0e28461 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28461
      have b0e54409 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e28462 X4 X1 X2 X3
           have i₂ := b0e37409 (M.op X1 (M.op X2 X3)) X0 X4
           grind)
        | (have i₁ := b0e28462 X2 X3 X4 x
           have i₂ := b0e37409 (M.op X3 (M.op X4 x)) (σ y) X2
           grind)
        | exact superpose b0e37409 b0e28462
        | exact resolve b0e28462 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28462
      have b0e54961 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X3 X1)) (M.op (M.op y X0) (M.op X1 (M.op X2 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e54263 X0 X1 X2 X3
           have i₂ := b0e37472 X0 (M.op X1 (M.op X2 X0))
           grind)
        | exact superpose b0e37472 b0e54263
        | exact resolve b0e54263 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54263
      have b0e56534 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 (M.op (M.op X1 (M.op X2 x)) X0))) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 (M.op X2 x) X1
           have i₂ := b0e54406 X2 (M.op X0 (M.op (M.op X1 (M.op X2 x)) X0))
           grind)
        | exact superpose b0e54406 b0e11
        | exact resolve b0e11 b0e54406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54406
      have b0e59487 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X6 X7) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1 X2 X3 X6 X7
        first
        | (have i₁ := b0e289 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x) (M.op X1 (M.op (M.op X2 X3) X1)) x x
           have i₂ := b0e117 X0 X1 X2 X3 x x
           grind)
        | exact superpose b0e117 b0e289
        | exact resolve b0e289 b0e117
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117 b0e289
      have b0e59987 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e59487 X0 X1 X2 X3 x x
           have i₂ := b0e54409 (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x) X1 (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
           grind)
        | exact superpose b0e54409 b0e59487
        | exact resolve b0e59487 b0e54409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59487
      have b0e60512 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (σ y) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e59987 X0 X1 x x
           have i₂ := b0e37409 X1 (M.op x x) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
           grind)
        | exact superpose b0e37409 b0e59987
        | exact resolve b0e59987 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59987
      have b0e60859 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e60512 X0 X1
           have i₂ := b0e37472 X1 (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
           grind)
        | exact superpose b0e37472 b0e60512
        | exact resolve b0e60512 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60512
      have b0e61098 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op (σ y) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e60859 X0 X1
           have i₂ := b0e37409 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))
           grind)
        | exact superpose b0e37409 b0e60859
        | exact resolve b0e60859 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e60859
      have b0e61276 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op y (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e61098 X0 X1
           have i₂ := b0e37472 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))
           grind)
        | exact superpose b0e37472 b0e61098
        | exact resolve b0e61098 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61098
      have b0e61396 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op y X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e61276 X0 X1
           have i₂ := b0e37921 X0 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op X0 (M.op X1 X0))
           grind)
        | exact superpose b0e37921 b0e61276
        | exact resolve b0e61276 b0e37921
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37921 b0e61276
      have b0e61473 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op y X0)) (M.op (M.op (σ y) X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e61396 X0 X1
           have i₂ := b0e37409 X0 (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))
           grind)
        | exact superpose b0e37409 b0e61396
        | exact resolve b0e61396 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61396
      have b0e61526 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op y X0)) (M.op (M.op y X0) (M.op X0 (M.op X1 X0))))) := by
        intro X0 X1
        first
        | (have i₁ := b0e61473 X0 X1
           have i₂ := b0e37472 X0 (M.op X0 (M.op X1 X0))
           grind)
        | exact superpose b0e37472 b0e61473
        | exact resolve b0e61473 b0e37472
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37472 b0e61473
      have b0e61558 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e61526 X0 X1
           have i₂ := b0e54961 X0 X0 X1 y
           grind)
        | exact superpose b0e54961 b0e61526
        | exact resolve b0e61526 b0e54961
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54961 b0e61526
      have b0e61580 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e61558 X0 X1
           have i₂ := b0e54409 (M.op y X0) X0 X1 X0 (M.op (M.op X0 (M.op X1 X0)) X0)
           grind)
        | exact superpose b0e54409 b0e61558
        | exact resolve b0e61558 b0e54409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61558
      have b0e63105 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) = (M.op X4 (M.op (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) (M.op X5 X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e31 (M.op X0 X1) X1 X2 X3
           have i₂ := b0e53956 X0 X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) X3
           grind)
        | (have i₁ := b0e31 (M.op X3 X1) X1 X2 X3
           have i₂ := b0e53956 X0 X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X3 X1)) X3
           grind)
        | exact superpose b0e53956 b0e31
        | exact resolve b0e31 b0e53956
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e63230 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) = (M.op X4 (M.op X1 (M.op X5 X1))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e63105 X0 X1 X2 X3 X4 X5
           have i₂ := b0e2250 X5 X1 (M.op X0 X1) (M.op X2 (M.op X3 X4))
           grind)
        | exact superpose b0e2250 b0e63105
        | exact resolve b0e63105 b0e2250
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63105
      have b0e99994 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op y (M.op (M.op (σ y) X0) (M.op (M.op X1 (M.op X2 x)) (M.op X3 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e56534 (M.op X3 X0) X1 X2
           have i₂ := b0e37409 X0 X3 (M.op (M.op X1 (M.op X2 x)) (M.op X3 X0))
           grind)
        | (have i₁ := b0e56534 (M.op (σ y) X0) X1 X2
           have i₂ := b0e37409 X0 X1 (M.op (M.op X1 (M.op X2 x)) (M.op (σ y) X0))
           grind)
        | exact superpose b0e37409 b0e56534
        | exact resolve b0e56534 b0e37409
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37409 b0e56534
      have b0e100082 : ∀ X0 X3 : G, (M.op X3 X0) = (M.op y (M.op x (M.op X0 (M.op X3 X0)))) := by
        intro X0 X3
        first
        | (have i₁ := b0e99994 X0 x x X3
           have i₂ := b0e63230 (σ y) X0 x x x X3
           grind)
        | exact superpose b0e63230 b0e99994
        | exact resolve b0e99994 b0e63230
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63230 b0e99994
      have b0e103846 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) = (M.op y (M.op x X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e100082 (M.op (M.op X1 (M.op X2 X0)) X0) X0
           have i₂ := b0e282 X0 X1 X2
           grind)
        | exact superpose b0e282 b0e100082
        | exact resolve b0e100082 b0e282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e282 b0e100082
      have b0e132760 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X0 X1) X1
           have i₂ := b0e61580 X1 X0
           grind)
        | exact superpose b0e61580 b0e11
        | exact resolve b0e11 b0e61580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e132940 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e53956 X2 X1 (M.op X1 X0) y
           have i₂ := b0e61580 X0 X1
           grind)
        | exact superpose b0e61580 b0e53956
        | exact resolve b0e53956 b0e61580
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61580
      have b0e133038 : ∀ X0 X1 X2 : G, (M.op y (M.op x X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e132940 X0 X1 X2
           have i₂ := b0e103846 X0 X0 X1
           grind)
        | exact superpose b0e103846 b0e132940
        | exact resolve b0e132940 b0e103846
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103846 b0e132940
      have b0e136256 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op (M.op y X1) (M.op X1 X0))) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2250 (M.op y X0) (M.op X0 X1) X2 (M.op X0 X1)
           have i₂ := b0e132760 X0 X1
           grind)
        | exact superpose b0e132760 b0e2250
        | exact resolve b0e2250 b0e132760
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2250 b0e132760
      have b0e136330 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op y (M.op x X0))) = X0 := by
        intro X0 X2
        first
        | (have i₁ := b0e136256 X0 x X2
           have i₂ := b0e133038 X0 x y
           grind)
        | exact superpose b0e133038 b0e136256
        | exact resolve b0e136256 b0e133038
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136256
      have b0e141503 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e9906 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e9906
        | exact resolve b0e9906 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9906
      have b0e141658 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e141503 X0
           have i₂ := b0e23 X0 (τ X0)
           grind)
        | exact superpose b0e23 b0e141503
        | (have j0 := b0e141503 X0
           grind)
        | exact resolve b0e141503 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e141503
      have b0e141686 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e141658 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e141658
        | (have j0 := b0e141658 X0
           grind)
        | exact resolve b0e141658 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141658
      have b0e141702 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e141686 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e141686 X0
           have r₂ := b0e14 X0 X0
           grind)
        | exact resolve b0e141686 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141686
      have b0e141740 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e141702 (σ X0)
           grind)
        | exact superpose b0e141702 b0e17
        | exact resolve b0e17 b0e141702
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e141764 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e141740 X0
           have i₂ := b0e141702 X0
           grind)
        | exact superpose b0e141702 b0e141740
        | exact resolve b0e141740 b0e141702
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141702 b0e141740
      have b0e143205 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) X2) = (M.op (σ (M.op X0 X0)) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e53956 X1 (σ X0) X2 (σ X0)
           have i₂ := b0e141764 X0
           grind)
        | exact superpose b0e141764 b0e53956
        | exact resolve b0e53956 b0e141764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53956
      have b0e143217 : ∀ X0 X1 : G, (M.op y (M.op x (σ X0))) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e133038 (σ X0) (σ X0) X1
           have i₂ := b0e141764 X0
           grind)
        | exact superpose b0e141764 b0e133038
        | exact resolve b0e133038 b0e141764
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149036 : ∀ X0 X1 : G, (M.op (M.op X0 (σ X1)) (σ (M.op X1 X1))) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e141764 (M.op X1 X1)
           have i₂ := b0e143205 X1 X0 (σ (M.op X1 X1))
           grind)
        | exact superpose b0e143205 b0e141764
        | exact resolve b0e141764 b0e143205
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141764 b0e143205
      have b0e149301 : ∀ X0 X1 : G, (M.op (M.op X0 (σ X1)) (σ (M.op X1 X1))) = (σ (M.op y (M.op x X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e149036 X0 X1
           have i₂ := b0e133038 X1 X1 X1
           grind)
        | exact superpose b0e133038 b0e149036
        | exact resolve b0e149036 b0e133038
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e133038 b0e149036
      have b0e149404 : ∀ X1 : G, (M.op y (M.op x (σ X1))) = (σ (M.op y (M.op x X1))) := by
        intro X1
        first
        | (have i₁ := b0e149301 x X1
           have i₂ := b0e143217 X1 x
           grind)
        | exact superpose b0e143217 b0e149301
        | exact resolve b0e149301 b0e143217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e143217 b0e149301
      have b0e151648 : (σ (M.op y x)) = (M.op y (M.op x (σ (M.op x y)))) := by
        first
        | (have i₁ := b0e149404 (M.op x y)
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e149404
        | exact resolve b0e149404 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e149404
      have b0e151718 : (σ y) = (M.op y (M.op x (σ (M.op x y)))) := by
        first
        | (have i₁ := b0e151648
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e151648
        | exact resolve b0e151648 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151648
      have b0e151920 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ y))) X0) = (M.op (M.op x (σ (M.op x y))) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e54409 X1 X2 y (M.op x (σ (M.op x y))) X0
           have i₂ := b0e151718
           grind)
        | exact superpose b0e151718 b0e54409
        | exact resolve b0e54409 b0e151718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54409
      have b0e151938 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ y))) X0) = (M.op (M.op y (σ (M.op x y))) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e151920 X0 X1 X2
           have i₂ := b0e37885 (σ (M.op x y)) X0
           grind)
        | exact superpose b0e37885 b0e151920
        | exact resolve b0e151920 b0e37885
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37885 b0e151920
      have b0e151966 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op y (σ (M.op x y))) X0) := by
        intro X0
        first
        | (have i₁ := b0e151938 X0 x x
           have i₂ := b0e54408 x x X0
           grind)
        | exact superpose b0e54408 b0e151938
        | exact resolve b0e151938 b0e54408
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54408 b0e151938
      have b0e155127 : (σ (M.op x y)) = (M.op (σ x) (M.op y (M.op x (σ (M.op x y))))) := by
        first
        | (have i₁ := b0e136330 (σ (M.op x y)) y
           have i₂ := b0e151966 (M.op y (M.op x (σ (M.op x y))))
           grind)
        | exact superpose b0e151966 b0e136330
        | exact resolve b0e136330 b0e151966
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e136330 b0e151966
      have b0e155397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e155127
           have i₂ := b0e151718
           grind)
        | exact superpose b0e151718 b0e155127
        | exact resolve b0e155127 b0e151718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151718 b0e155127
      have b0e155418 : False := by grind
      exact b0e155418
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e26 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = X0 := by
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
        have b1e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b1e12 X0 X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X1 X3
             have i₂ := b1e12 X0 (M.op X3 X1) X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : x = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b1e26 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e26
          | exact resolve b1e26 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b1e37 : (k x y) = (M.op x x) := by grind
        clear b1e36
        have b1e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e50 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (M.op x y) x
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e12
          | exact resolve b1e12 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e53 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e55 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e53
             have r₂ := b1e21
             grind)
          | exact resolve b1e53 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e56 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e57 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e37
             grind)
          | exact superpose b1e37 b1e56
          | exact resolve b1e56 b1e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e56
        have b1e60 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e13
          | exact resolve b1e13 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e61 : y = (M.op x x) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e60
          | exact resolve b1e60 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e122 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X4 (M.op (M.op X0 (M.op X1 X0)) X4))) = X4 := by
          intro X0 X1 X4
          first
          | (have i₁ := b1e28 (M.op X0 (M.op X1 X0)) X1 (M.op (M.op x x) X1) X4
             have i₂ := b1e28 X1 x x X0
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e129 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ x) (M.op (M.op X0 X1) (σ x))) (M.op (σ x) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 (σ x) X0 X1 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e28
          | exact resolve b1e28 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e130 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op (σ x) (M.op (M.op X1 X2) (σ x))) (M.op (M.op X0 (M.op (σ y) X0)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28 (σ x) X1 X2 (M.op X0 (M.op (σ y) X0))
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e28
          | exact resolve b1e28 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e131 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x (M.op (M.op X1 X2) x)) (M.op (M.op X0 (M.op y X0)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e28 x X1 X2 (M.op X0 (M.op y X0))
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e28
          | exact resolve b1e28 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e133 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 x X0 X1 x
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e28
          | exact resolve b1e28 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e137 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X3 X0)) (M.op (M.op X1 X2) X3) X3
             have i₂ := b1e28 X3 X1 X2 X0
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
             have i₂ := b1e28 X1 x x X0
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e283 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X4 (M.op (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) X4)) = (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op (M.op X4 (M.op (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) X4)) X4)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e29 X0 (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X0) X2 X1
             have i₂ := b1e29 X0 X1 X2 X3
             grind)
          | exact superpose b1e29 b1e29
          | exact resolve b1e29 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e304 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (M.op X1 (M.op X0 X1)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 X0 (M.op (σ y) X0) (σ x) X0
             have i₂ := b1e27 X0
             grind)
          | exact superpose b1e27 b1e29
          | exact resolve b1e29 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e320 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 (M.op (M.op X1 (M.op X2 X0)) X0) X0
             have i₂ := b1e29 X0 X0 X1 X2
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e323 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e28 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3 X4 X0
             have i₂ := b1e29 X0 X0 X1 X2
             grind)
          | exact superpose b1e29 b1e28
          | exact resolve b1e28 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e327 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) = (M.op (M.op X3 (M.op (M.op X4 X5) X3)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e28 X3 X4 X5 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)
             have i₂ := b1e29 X0 X3 X1 X2
             grind)
          | exact superpose b1e29 b1e28
          | exact resolve b1e28 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e331 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) = (M.op X4 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) X4 X3
             have i₂ := b1e29 X0 (M.op X3 X4) X1 X2
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e332 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) = (M.op (σ x) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e27 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)
             have i₂ := b1e29 X0 (σ y) X1 X2
             grind)
          | exact superpose b1e29 b1e27
          | exact resolve b1e27 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e422 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 (σ X1) (σ X0)
             have i₂ := b1e43 X1 X0
             grind)
          | exact superpose b1e43 b1e15
          | (have j0 := b1e15 (σ X1) (σ X0)
             have j1 := b1e43 X1 X0
             grind)
          | (have r₁ := b1e15 (σ X1) (σ X1)
             have r₂ := b1e43 X1 X1
             grind)
          | (have r₁ := b1e15 (σ X0) (σ X1)
             have r₂ := b1e43 X0 X1
             grind)
          | exact resolve b1e15 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e432 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b1e422 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422
        have b1e444 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e432 X0 X1
             have i₂ := b1e18 X1 X0
             grind)
          | exact superpose b1e18 b1e432
          | (have j0 := b1e432 X0 X1
             grind)
          | exact resolve b1e432 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e432
        have b1e827 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 y)) y) := by
          intro X0
          first
          | (have i₁ := b1e139 y X0 (M.op x y)
             have i₂ := b1e50 y
             grind)
          | exact superpose b1e50 b1e139
          | exact resolve b1e139 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e1500 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
          first
          | (have i₁ := b1e304 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e304
          | exact resolve b1e304 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1521 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op (σ y) X0) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e304 X0 y
             have i₂ := b1e827 X0
             grind)
          | exact superpose b1e827 b1e304
          | exact resolve b1e304 b1e827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e827
        have b1e1828 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) = (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e122 X0 X1 (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0)))
             have i₂ := b1e139 (M.op X1 X0) X0 (M.op X0 (M.op X1 X0))
             grind)
          | exact superpose b1e139 b1e122
          | exact resolve b1e122 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e2368 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 y)) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e26 (M.op (M.op X0 (M.op X1 y)) y)
             have i₂ := b1e320 y X0 X1
             grind)
          | exact superpose b1e320 b1e26
          | exact resolve b1e26 b1e320
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e320
        have b1e2659 : ∀ X0 X1 : G, (M.op y (M.op y y)) = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e131 y X0 X1
             have i₂ := b1e2368 y y
             grind)
          | exact superpose b1e2368 b1e131
          | exact resolve b1e131 b1e2368
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e131 b1e2368
        have b1e2725 : x = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b1e2659 x x
             have i₂ := b1e133 x x
             grind)
          | exact superpose b1e133 b1e2659
          | exact resolve b1e2659 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133 b1e2659
        have b1e2753 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) x) := by
          intro X0
          first
          | (have i₁ := b1e139 y X0 y
             have i₂ := b1e2725
             grind)
          | exact superpose b1e2725 b1e139
          | exact resolve b1e139 b1e2725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e2800 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b1e12 x (M.op X0 y) y
             have i₂ := b1e2753 X0
             grind)
          | exact superpose b1e2753 b1e12
          | exact resolve b1e12 b1e2753
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2753
        have b1e9182 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e444 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e444
        have b1e9184 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b1e9182 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9182
        have b1e27566 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e29 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X5 X3 X4
             have i₂ := b1e323 X0 X1 X2 X3 (M.op X4 X5)
             grind)
          | exact superpose b1e323 b1e29
          | exact resolve b1e29 b1e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e27571 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) = (M.op (M.op (M.op X5 X6) (M.op X3 X4)) X0) := by
          intro X0 X1 X2 X3 X4 X5 X6
          first
          | (have i₁ := b1e137 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X5 X6 (M.op X3 X4)
             have i₂ := b1e323 X0 X1 X2 X3 X4
             grind)
          | exact superpose b1e323 b1e137
          | exact resolve b1e137 b1e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137
        have b1e27576 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) = (M.op (M.op (σ y) (M.op X3 X4)) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e304 (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))
             have i₂ := b1e323 X0 X1 X2 X3 X4
             grind)
          | exact superpose b1e323 b1e304
          | exact resolve b1e304 b1e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e323
        have b1e27679 : ∀ X0 X3 X4 X5 X6 : G, (M.op (M.op (M.op X5 X6) (M.op X3 X4)) X0) = (M.op (M.op (σ y) (M.op X3 X4)) X0) := by
          intro X0 X3 X4 X5 X6
          first
          | (have i₁ := b1e27571 X0 x x X3 X4 X5 X6
             have i₂ := b1e27576 X0 x x X3 X4
             grind)
          | exact superpose b1e27576 b1e27571
          | exact resolve b1e27571 b1e27576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27571
        have b1e27684 : ∀ X0 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op (σ y) (M.op X3 (M.op X4 X5))) X0) := by
          intro X0 X3 X4 X5
          first
          | (have i₁ := b1e27566 X0 x x X3 X4 X5
             have i₂ := b1e27576 X0 x x X3 (M.op X4 X5)
             grind)
          | exact superpose b1e27576 b1e27566
          | exact resolve b1e27566 b1e27576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27566 b1e27576
        have b1e46622 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) = (M.op (σ x) (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e332 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (σ y) (M.op x x)
             have i₂ := b1e327 X0 X1 X2 (σ y) x x
             grind)
          | exact superpose b1e327 b1e332
          | exact resolve b1e332 b1e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e46840 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) = (M.op (σ x) (M.op (M.op (σ y) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e46622 X0 X1 X2
             have i₂ := b1e27679 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)
             grind)
          | exact superpose b1e27679 b1e46622
          | exact resolve b1e46622 b1e27679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46622
        have b1e47319 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) = (M.op (σ x) (M.op (M.op (M.op X1 (M.op X2 (σ y))) X0) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e46840 X0 X1 X2
             have i₂ := b1e27684 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)
             grind)
          | (have i₁ := b1e46840 X0 X1 X2
             have i₂ := b1e27684 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) x x (M.op (σ y) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))))
             grind)
          | exact superpose b1e27684 b1e46840
          | exact resolve b1e46840 b1e27684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46840
        have b1e47640 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) = (M.op (σ x) (M.op (M.op (M.op X1 (M.op X2 (σ y))) X0) (M.op (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e47319 x X1 X2
             have i₂ := b1e27679 (M.op (M.op x (M.op (M.op X1 (M.op X2 (σ y))) x)) x) x (M.op (M.op X1 (M.op X2 (σ y))) x) (M.op x (M.op (M.op X1 (M.op X2 (σ y))) x)) x
             grind)
          | exact superpose b1e27679 b1e47319
          | exact resolve b1e47319 b1e27679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47319
        have b1e47806 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) = (M.op (σ x) (M.op (M.op (M.op X1 (M.op X2 (σ y))) X0) (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e47640 X0 X1 X2
             have i₂ := b1e27684 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) x x (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))
             grind)
          | (have i₁ := b1e47640 x X1 X2
             have i₂ := b1e27684 (M.op (M.op x (M.op (M.op X1 (M.op X2 (σ y))) x)) x) x (M.op X1 (M.op X2 (σ y))) x
             grind)
          | exact superpose b1e27684 b1e47640
          | exact resolve b1e47640 b1e27684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47640
        have b1e47871 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e47806 X0 X1 X2
             have i₂ := b1e12 X0 (M.op (M.op X1 (M.op X2 (σ y))) X0) X0
             grind)
          | exact superpose b1e12 b1e47806
          | exact resolve b1e47806 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47806
        have b1e47901 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)) X0)) (M.op (M.op (M.op X1 (M.op X2 (σ y))) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (σ y))) X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e47871 X0 X1 X2
             have i₂ := b1e1828 X0 (M.op X1 (M.op X2 (σ y)))
             grind)
          | exact superpose b1e1828 b1e47871
          | exact resolve b1e47871 b1e1828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47871
        have b1e47919 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (M.op X1 (M.op X2 (σ y))) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e47901 X0 X1 X2
             have i₂ := b1e28 X0 X0 (M.op (M.op X1 (M.op X2 (σ y))) X0) (M.op (M.op X1 (M.op X2 (σ y))) X0)
             grind)
          | exact superpose b1e28 b1e47901
          | exact resolve b1e47901 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47901
        have b1e48988 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) = (M.op X4 (M.op (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e331 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op X3 X4) (M.op X4 x) X3 X4
             have i₂ := b1e327 X0 X1 X2 (M.op X3 X4) X4 x
             grind)
          | exact superpose b1e327 b1e331
          | exact resolve b1e331 b1e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e327
        have b1e49333 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) = (M.op X4 (M.op (M.op (σ y) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e48988 X0 X1 X2 X3 X4
             have i₂ := b1e27679 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)
             grind)
          | exact superpose b1e27679 b1e48988
          | exact resolve b1e48988 b1e27679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48988
        have b1e49664 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49333 X0 X1 X2 X3 X4
             have i₂ := b1e27684 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)
             grind)
          | (have i₁ := b1e49333 X0 X1 X2 X3 X4
             have i₂ := b1e27684 (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) X3 X4 (M.op (σ y) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))))
             grind)
          | exact superpose b1e27684 b1e49333
          | exact resolve b1e49333 b1e27684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49333
        have b1e49798 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) (M.op (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49664 X3 X1 X2 X3 X4
             have i₂ := b1e27679 (M.op (M.op X3 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X3)) X3) X3 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X3) (M.op X3 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X3)) X3
             grind)
          | exact superpose b1e27679 b1e49664
          | exact resolve b1e49664 b1e27679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27679 b1e49664
        have b1e49872 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) = (M.op X4 (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49798 X0 X1 X2 X3 X4
             have i₂ := b1e27684 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) X3 X4 (M.op (σ y) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))
             grind)
          | (have i₁ := b1e49798 x X1 X2 X3 X4
             have i₂ := b1e27684 (M.op (M.op x (M.op (M.op X1 (M.op X2 (M.op X3 X4))) x)) x) x (M.op X1 (M.op X2 (M.op X3 X4))) x
             grind)
          | exact superpose b1e27684 b1e49798
          | exact resolve b1e49798 b1e27684
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27684 b1e49798
        have b1e49926 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49872 X0 X1 X2 X3 X4
             have i₂ := b1e12 X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) X0
             grind)
          | exact superpose b1e12 b1e49872
          | exact resolve b1e49872 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49872
        have b1e49949 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)) X0)) (M.op (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49926 X0 X1 X2 X3 X4
             have i₂ := b1e1828 X0 (M.op X1 (M.op X2 (M.op X3 X4)))
             grind)
          | exact superpose b1e1828 b1e49926
          | exact resolve b1e49926 b1e1828
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1828 b1e49926
        have b1e49966 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e49949 X0 X1 X2 X3 X4
             have i₂ := b1e28 X0 X0 (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0)
             grind)
          | exact superpose b1e28 b1e49949
          | exact resolve b1e49949 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e49949
        have b1e50117 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (M.op (M.op X0 X1) (σ x))) (M.op (σ x) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e130 (σ y) X0 X1
             have i₂ := b1e47919 (σ y) (σ y) (σ y)
             grind)
          | exact superpose b1e47919 b1e130
          | exact resolve b1e130 b1e47919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e130 b1e47919
        have b1e50543 : (σ x) = (M.op (σ y) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b1e50117 x x
             have i₂ := b1e129 x x
             grind)
          | exact superpose b1e129 b1e50117
          | exact resolve b1e50117 b1e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e129 b1e50117
        have b1e53717 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X1) = (M.op (M.op X0 (M.op y X0)) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e49966 X1 X2 X3 x (M.op X0 (M.op y X0))
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e49966
          | exact resolve b1e49966 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e53777 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X2) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e49966 X2 X1 (M.op X3 (M.op x X3)) X0 (M.op X3 X0)
             have i₂ := b1e139 X3 x X0
             grind)
          | exact superpose b1e139 b1e49966
          | exact resolve b1e49966 b1e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e53839 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 (σ x)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e49966 X0 X1 (σ y) (σ y) (σ y)
             have i₂ := b1e50543
             grind)
          | exact superpose b1e50543 b1e49966
          | exact resolve b1e49966 b1e50543
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50543
        have b1e53840 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (M.op y X0) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e49966 X1 X2 x X0 (M.op y X0)
             have i₂ := b1e26 X0
             grind)
          | exact superpose b1e26 b1e49966
          | exact resolve b1e49966 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e53968 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X2) (M.op X0 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op X2 (M.op X1 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e304 X2 (M.op X1 X0)
             have i₂ := b1e49966 (M.op X1 X0) (M.op X1 X0) X2 X1 X0
             grind)
          | exact superpose b1e49966 b1e304
          | exact resolve b1e304 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304
        have b1e53992 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 (M.op X2 (M.op X3 X0)) x
             have i₂ := b1e49966 X1 x X2 X3 X0
             grind)
          | exact superpose b1e49966 b1e12
          | exact resolve b1e12 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e60775 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2))) = X2 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e12 X2 (M.op X4 X1) X3
             have i₂ := b1e53777 X1 X0 (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2)) X4
             grind)
          | (have i₁ := b1e12 X2 (M.op X4 X1) X3
             have i₂ := b1e53777 X1 X4 (M.op X2 (M.op (M.op X3 (M.op X4 X1)) X2)) X0
             grind)
          | exact superpose b1e53777 b1e12
          | exact resolve b1e12 b1e53777
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e73816 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X1) = (M.op (M.op X4 (M.op X5 X2)) (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e53992 X2 (M.op X3 X1) X4 X5
             have i₂ := b1e53777 X1 X0 (M.op X2 (M.op X3 X1)) X3
             grind)
          | (have i₁ := b1e53992 X2 (M.op X3 X1) X4 X5
             have i₂ := b1e53777 X1 X3 (M.op X2 (M.op X3 X1)) X0
             grind)
          | exact superpose b1e53777 b1e53992
          | exact resolve b1e53992 b1e53777
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53992
        have b1e81022 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) = (M.op (M.op (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)) X5) (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))))) := by
          intro X0 X1 X2 X3 X4 X5 X6 X7 X8
          first
          | (have i₁ := b1e283 X0 X1 X2 X3 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))))) X0))) X5
             have i₂ := b1e331 X0 X1 X2 X3 (M.op X5 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))
             grind)
          | exact superpose b1e331 b1e283
          | exact resolve b1e283 b1e331
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e331
        have b1e81165 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0)) = (M.op (σ x) (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e332 (M.op (M.op X4 (M.op (M.op X5 (M.op (M.op X2 (σ y)) (M.op (M.op X1 (M.op X2 X3)) (M.op X2 (σ y))))) X4)) X4) (M.op (M.op X2 (σ y)) (M.op (M.op X1 (M.op X2 X3)) (M.op X2 (σ y)))) X2
             have i₂ := b1e283 (M.op X2 (σ y)) X1 X2 X3 X4 X5
             grind)
          | exact superpose b1e283 b1e332
          | exact resolve b1e332 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e332
        have b1e81175 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4))))) X0)) = (M.op X4 (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4))))) X0)) X0)) := by
          intro X0 X1 X2 X3 X4 X5 X6 X7
          first
          | (have i₁ := b1e49966 (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4))))) X0)) X0) (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4)))) X2 X3 X4
             have i₂ := b1e283 (M.op X2 (M.op X3 X4)) X5 X6 X7 X0 X1
             grind)
          | exact superpose b1e283 b1e49966
          | exact resolve b1e49966 b1e283
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e283
        have b1e81403 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op X4 (M.op (M.op X0 (M.op y X0)) X0)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4))))) X0)) := by
          intro X0 X1 X2 X3 X4 X5 X6 X7
          first
          | (have i₁ := b1e81175 X0 X1 X2 X3 X4 X5 X6 X7
             have i₂ := b1e53717 X0 X0 X0 (M.op X1 (M.op (M.op X2 (M.op X3 X4)) (M.op (M.op X5 (M.op X6 X7)) (M.op X2 (M.op X3 X4)))))
             grind)
          | exact superpose b1e53717 b1e81175
          | exact resolve b1e81175 b1e53717
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53717 b1e81175
        have b1e81411 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0)) = (M.op (σ x) (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b1e81165 X0 X1 X2 X3 X4 X5
             have i₂ := b1e73816 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0 X0 (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))) (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (σ y)) (M.op (M.op X3 (M.op X4 X5)) (M.op X2 (σ y))))) X0))
             grind)
          | exact superpose b1e73816 b1e81165
          | exact resolve b1e81165 b1e73816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81165
        have b1e81520 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) = (M.op (M.op y X5) (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))))) := by
          intro X0 X1 X2 X3 X4 X5 X6 X7 X8
          first
          | (have i₁ := b1e81022 X0 X1 X2 X3 X4 X5 X6 X7 X8
             have i₂ := b1e53840 X5 (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)))) (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5))
             grind)
          | exact superpose b1e53840 b1e81022
          | exact resolve b1e81022 b1e53840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81022
        have b1e81708 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X4)) X0)) = (M.op X4 (M.op (M.op X0 (M.op y X0)) X0)) := by
          intro X0 X2 X3 X4
          first
          | (have i₁ := b1e81403 X0 x X2 X3 X4 x x x
             have i₂ := b1e49966 X0 x (M.op X2 (M.op X3 X4)) (M.op x (M.op x x)) (M.op X2 (M.op X3 X4))
             grind)
          | exact superpose b1e49966 b1e81403
          | exact resolve b1e81403 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81403
        have b1e81716 : ∀ X0 X2 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X2 (σ y)) X0)) X0) (M.op X0 (M.op (M.op X2 (σ y)) X0))) (M.op (M.op X0 (M.op (M.op X2 (σ y)) X0)) X0)) = (M.op (σ x) (M.op (M.op X2 (σ y)) X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e81411 X0 x X2 x x x
             have i₂ := b1e49966 X0 x (M.op X2 (σ y)) (M.op x (M.op x x)) (M.op X2 (σ y))
             grind)
          | exact superpose b1e49966 b1e81411
          | exact resolve b1e81411 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81411
        have b1e81818 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0)) = (M.op (M.op y X5) (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) := by
          intro X0 X1 X2 X3 X4 X5 X6 X7 X8
          first
          | (have i₁ := b1e81520 X0 X1 X2 X3 X4 X5 X6 X7 X8
             have i₂ := b1e73816 (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0 X0 (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))))) X0))
             grind)
          | exact superpose b1e73816 b1e81520
          | exact resolve b1e81520 b1e73816
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e73816 b1e81520
        have b1e81974 : ∀ X0 X2 : G, (M.op (σ x) (M.op (M.op X2 (σ y)) X0)) = (M.op X0 (M.op (M.op X0 (M.op (M.op X2 (σ y)) X0)) X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e81716 X0 X2
             have i₂ := b1e49966 (M.op (M.op X0 (M.op (M.op X2 (σ y)) X0)) X0) (M.op (M.op X0 (M.op (M.op X2 (σ y)) X0)) X0) X0 (M.op X2 (σ y)) X0
             grind)
          | exact superpose b1e49966 b1e81716
          | exact resolve b1e81716 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81716
        have b1e82048 : ∀ X0 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5))) X0)) X0) (M.op X0 (M.op (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5))) X0))) (M.op (M.op X0 (M.op (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5))) X0)) X0)) = (M.op (M.op y X5) (M.op (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5))) X0)) := by
          intro X0 X4 X5 X6 X7 X8
          first
          | (have i₁ := b1e81818 X0 x x x X4 X5 X6 X7 X8
             have i₂ := b1e49966 X0 x x x (M.op X4 (M.op X5 (M.op (M.op X6 (M.op X7 X8)) X5)))
             grind)
          | exact superpose b1e49966 b1e81818
          | exact resolve b1e81818 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81818
        have b1e82194 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op X0 (M.op y X0)) X0)) = (M.op (σ x) (M.op (M.op X2 (σ y)) X0)) := by
          intro X0 X2
          first
          | (have i₁ := b1e81974 X0 X2
             have i₂ := b1e81708 X0 X0 (M.op X2 (σ y)) X0
             grind)
          | exact superpose b1e81708 b1e81974
          | exact resolve b1e81974 b1e81708
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81708 b1e81974
        have b1e82245 : ∀ X0 X5 : G, (M.op (M.op (M.op (M.op X0 (M.op X5 X0)) X0) (M.op X0 (M.op X5 X0))) (M.op (M.op X0 (M.op X5 X0)) X0)) = (M.op (M.op y X5) (M.op X5 X0)) := by
          intro X0 X5
          first
          | (have i₁ := b1e82048 X0 x x x x x
             have i₂ := b1e49966 X0 x x (M.op x (M.op x x)) x
             grind)
          | exact superpose b1e49966 b1e82048
          | exact resolve b1e82048 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82048
        have b1e82395 : ∀ X0 X5 : G, (M.op (M.op y X5) (M.op X5 X0)) = (M.op X0 (M.op (M.op X0 (M.op X5 X0)) X0)) := by
          intro X0 X5
          first
          | (have i₁ := b1e82245 X0 X5
             have i₂ := b1e49966 (M.op (M.op X0 (M.op X5 X0)) X0) (M.op (M.op X0 (M.op X5 X0)) X0) X0 X5 X0
             grind)
          | exact superpose b1e49966 b1e82245
          | exact resolve b1e82245 b1e49966
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49966 b1e82245
        have b1e97001 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op (M.op X1 X0) (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e53777 X0 (σ y) (M.op x y) X1
             have i₂ := b1e1521 X0
             grind)
          | exact superpose b1e1521 b1e53777
          | exact resolve b1e53777 b1e1521
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1521
        have b1e137003 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 X1) X1
             have i₂ := b1e82395 X1 X0
             grind)
          | exact superpose b1e82395 b1e12
          | exact resolve b1e12 b1e82395
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82395
        have b1e141682 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e9184 (τ X0)
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e9184
          | exact resolve b1e9184 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9184
        have b1e141864 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e141682 X0
             have i₂ := b1e25 X0 (τ X0)
             grind)
          | exact superpose b1e25 b1e141682
          | (have j0 := b1e141682 X0
             grind)
          | exact resolve b1e141682 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e141682
        have b1e141894 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e141864 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e141864
          | (have j0 := b1e141864 X0
             grind)
          | exact resolve b1e141864 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141864
        have b1e141903 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e141894 X0
             have j1 := b1e15 X0 X0
             grind)
          | (have r₁ := b1e141894 X0
             have r₂ := b1e15 X0 X0
             grind)
          | exact resolve b1e141894 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141894
        have b1e141945 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e141903 (σ X0)
             grind)
          | exact superpose b1e141903 b1e18
          | exact resolve b1e18 b1e141903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141977 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e141945 X0
             have i₂ := b1e141903 X0
             grind)
          | exact superpose b1e141903 b1e141945
          | exact resolve b1e141945 b1e141903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141903 b1e141945
        have b1e143765 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e53777 (σ X0) X2 X1 (σ X0)
             have i₂ := b1e141977 X0
             grind)
          | exact superpose b1e141977 b1e53777
          | exact resolve b1e53777 b1e141977
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53777
        have b1e159648 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ (M.op x y))) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e143765 (M.op x y) X1 X0
             have i₂ := b1e2800 x
             grind)
          | exact superpose b1e2800 b1e143765
          | exact resolve b1e143765 b1e2800
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2800 b1e143765
        have b1e167356 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op X0 (M.op (σ x) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ (M.op x y)) x
             have i₂ := b1e159648 x X0
             grind)
          | exact superpose b1e159648 b1e12
          | exact resolve b1e12 b1e159648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e167417 : ∀ X0 : G, (M.op (M.op (σ (M.op x y)) X0) (M.op (σ x) (M.op (σ (M.op x y)) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e137003 (σ (M.op x y)) X0
             have i₂ := b1e159648 y (M.op (σ (M.op x y)) X0)
             grind)
          | exact superpose b1e159648 b1e137003
          | exact resolve b1e137003 b1e159648
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137003 b1e159648
        have b1e167712 : ∀ X0 : G, (M.op (M.op (σ y) (σ x)) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e167417 X0
             have i₂ := b1e53968 X0 (σ (M.op x y)) (σ x)
             grind)
          | exact superpose b1e53968 b1e167417
          | exact resolve b1e167417 b1e53968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53968 b1e167417
        have b1e167742 : ∀ X0 : G, (M.op (M.op y (σ x)) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e167712 X0
             have i₂ := b1e53840 (σ x) (M.op X0 (M.op (σ (M.op x y)) X0)) (σ y)
             grind)
          | exact superpose b1e53840 b1e167712
          | exact resolve b1e167712 b1e53840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167712
        have b1e167749 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (σ (M.op x y)) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e167742 X0
             have i₂ := b1e53839 (M.op X0 (M.op (σ (M.op x y)) X0)) y
             grind)
          | exact superpose b1e53839 b1e167742
          | exact resolve b1e167742 b1e53839
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167742
        have b1e180033 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ (M.op x y)) (M.op (M.op (M.op X1 (σ y)) X0) (M.op X0 (M.op (M.op X0 (M.op y X0)) X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e167356 (M.op (M.op X1 (σ y)) X0)
             have i₂ := b1e82194 X0 X1
             grind)
          | exact superpose b1e82194 b1e167356
          | exact resolve b1e167356 b1e82194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82194 b1e167356
        have b1e180245 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) X0) = (M.op (σ (M.op x y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e180033 X0 X1
             have i₂ := b1e60775 (M.op X1 (σ y)) X0 X0 X0 y
             grind)
          | exact superpose b1e60775 b1e180033
          | exact resolve b1e180033 b1e60775
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60775 b1e180033
        have b1e180476 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op (M.op x y) (M.op x y))))) := by
          first
          | (have i₁ := b1e167749 (σ (M.op x y))
             have i₂ := b1e141977 (M.op x y)
             grind)
          | exact superpose b1e141977 b1e167749
          | exact resolve b1e167749 b1e141977
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141977 b1e167749
        have b1e180667 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op y (M.op y y))))) := by
          first
          | (have i₁ := b1e180476
             have i₂ := b1e97001 y x
             grind)
          | exact superpose b1e97001 b1e180476
          | exact resolve b1e180476 b1e97001
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e97001 b1e180476
        have b1e180687 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b1e180667
             have i₂ := b1e2725
             grind)
          | exact superpose b1e2725 b1e180667
          | exact resolve b1e180667 b1e2725
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2725 b1e180667
        have b1e198659 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ x)) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b1e1500
             have i₂ := b1e180245 (σ x) (σ x)
             grind)
          | exact superpose b1e180245 b1e1500
          | exact resolve b1e1500 b1e180245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1500 b1e180245
        have b1e199341 : (M.op (σ x) (σ y)) = (M.op (M.op y (σ x)) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b1e198659
             have i₂ := b1e53840 (σ x) (M.op (σ (M.op x y)) (σ x)) (σ y)
             grind)
          | exact superpose b1e53840 b1e198659
          | exact resolve b1e198659 b1e53840
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53840 b1e198659
        have b1e199429 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ x))) := by
          first
          | (have i₁ := b1e199341
             have i₂ := b1e53839 (M.op (σ (M.op x y)) (σ x)) y
             grind)
          | exact superpose b1e53839 b1e199341
          | exact resolve b1e199341 b1e53839
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53839 b1e199341
        have b1e199449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e199429
             have i₂ := b1e180687
             grind)
          | exact superpose b1e180687 b1e199429
          | exact resolve b1e199429 b1e180687
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e180687 b1e199429
        have b1e199453 : False := by grind
        exact b1e199453
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e26 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X1 X3
             have i₂ := b2e12 X0 (M.op X3 X1) X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b2e35 : (k x y) = (M.op x x) := by grind
        clear b2e32
        have b2e39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e44 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X4 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X4))) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e27 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X2 X3 X4
             have i₂ := b2e12 X0 (M.op X2 X3) X1
             grind)
          | exact superpose b2e12 b2e27
          | exact resolve b2e27 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X4 X5) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e27 (M.op X1 (M.op (M.op X2 X3) X1)) X4 X5 (M.op X0 (M.op X1 X0))
             have i₂ := b2e27 X1 X2 X3 X0
             grind)
          | exact superpose b2e27 b2e27
          | exact resolve b2e27 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e94 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
             have i₂ := b2e27 X1 x x X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e138 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e44 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e139 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e138
             have r₂ := b2e21
             grind)
          | exact resolve b2e138 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e138
        have b2e140 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e139
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e139
          | exact resolve b2e139 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e139
        have b2e141 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e140
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e140
          | exact resolve b2e140 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e140
        have b2e142 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e141
             grind)
          | exact superpose b2e141 b2e19
          | exact resolve b2e19 b2e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e201 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X1 (M.op X0 X1)) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e28 X0 (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X0)) x
             have i₂ := b2e27 X0 X1 X2 x
             grind)
          | exact superpose b2e27 b2e28
          | exact resolve b2e28 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e203 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op y X0) (M.op (M.op X1 (M.op X0 X1)) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e28 X0 (M.op y X0) x X0
             have i₂ := b2e26 X0
             grind)
          | exact superpose b2e26 b2e28
          | exact resolve b2e28 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e215 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 (M.op (M.op X1 (M.op X2 X0)) X0) X0
             have i₂ := b2e28 X0 X0 X1 X2
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e217 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e27 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3 X4 X0
             have i₂ := b2e28 X0 X0 X1 X2
             grind)
          | exact superpose b2e28 b2e27
          | exact resolve b2e27 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e219 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) = (M.op (M.op X3 (M.op (M.op X4 X5) X3)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e27 X3 X4 X5 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)
             have i₂ := b2e28 X0 X3 X1 X2
             grind)
          | exact superpose b2e28 b2e27
          | exact resolve b2e27 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e334 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e39 X1 X0
             grind)
          | exact superpose b2e39 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e39 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X1) (σ X1)
             have r₂ := b2e39 X1 X1
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e39 X0 X1
             grind)
          | exact resolve b2e15 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e344 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e334 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e334
        have b2e354 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e344 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e344
          | (have j0 := b2e344 X0 X1
             grind)
          | exact resolve b2e344 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e344
        have b2e537 : ∀ X0 : G, (M.op (M.op (σ y) (σ (M.op x x))) (M.op X0 (M.op (σ y) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e94 (σ y) (σ x) X0
             have i₂ := b2e141
             grind)
          | exact superpose b2e141 b2e94
          | exact resolve b2e94 b2e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e564 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 (σ x))) (M.op (σ y) (σ (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b2e94 (σ x) X0 (σ y)
             have i₂ := b2e141
             grind)
          | exact superpose b2e141 b2e94
          | exact resolve b2e94 b2e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2032 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) X1 X0
             have i₂ := b2e215 (M.op X0 X1) X2 X3
             grind)
          | exact superpose b2e215 b2e12
          | exact resolve b2e12 b2e215
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e215
        have b2e8299 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e354 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e354
        have b2e8301 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e8299 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8299
        have b2e21726 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e28 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X5 X3 X4
             have i₂ := b2e217 X0 X1 X2 X3 (M.op X4 X5)
             grind)
          | exact superpose b2e217 b2e28
          | exact resolve b2e28 b2e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e21740 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) = (M.op (M.op y (M.op X3 X4)) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e203 (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))
             have i₂ := b2e217 X0 X1 X2 X3 X4
             grind)
          | exact superpose b2e217 b2e203
          | exact resolve b2e203 b2e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e203 b2e217
        have b2e21845 : ∀ X0 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op y (M.op X3 (M.op X4 X5))) X0) := by
          intro X0 X3 X4 X5
          first
          | (have i₁ := b2e21726 X0 x x X3 X4 X5
             have i₂ := b2e21740 X0 x x X3 (M.op X4 X5)
             grind)
          | exact superpose b2e21740 b2e21726
          | exact resolve b2e21726 b2e21740
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21726 b2e21740
        have b2e24757 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e21845 X2 (M.op X1 (M.op x X1)) X0 (M.op X1 X0)
             have i₂ := b2e94 X1 x X0
             grind)
          | exact superpose b2e94 b2e21845
          | exact resolve b2e21845 b2e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26066 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e24757 x X0 X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e24757
          | exact resolve b2e24757 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26086 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e24757 X1 X0 X2
             have i₂ := b2e24757 X1 X3 X2
             grind)
          | (have i₁ := b2e24757 X0 X1 X2
             have i₂ := b2e24757 X0 y X2
             grind)
          | exact superpose b2e24757 b2e24757
          | exact resolve b2e24757 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y X0) (M.op X1 (M.op X2 X0))) = (M.op (M.op X3 X1) (M.op (M.op (M.op y X0) (M.op X1 (M.op X2 X0))) (M.op X2 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e201 X0 (M.op X1 X0) X2
             have i₂ := b2e24757 X0 X1 (M.op X0 (M.op X1 X0))
             grind)
          | (have i₁ := b2e201 X0 (M.op y X0) X2
             have i₂ := b2e24757 X0 X1 (M.op X0 (M.op y X0))
             grind)
          | exact superpose b2e24757 b2e201
          | exact resolve b2e201 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26483 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e21845 X4 X1 X2 X3
             have i₂ := b2e24757 (M.op X1 (M.op X2 X3)) X0 X4
             grind)
          | (have i₁ := b2e21845 X2 X3 X4 x
             have i₂ := b2e24757 (M.op X3 (M.op X4 x)) y X2
             grind)
          | exact superpose b2e24757 b2e21845
          | exact resolve b2e21845 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e21845
        have b2e26889 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X0 (M.op X2 X0))) = (M.op (M.op y X0) (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26368 X0 X1 X2 X3
             have i₂ := b2e2032 X2 X0 (M.op y X0) X1
             grind)
          | exact superpose b2e2032 b2e26368
          | exact resolve b2e26368 b2e2032
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2032 b2e26368
        have b2e27749 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) (M.op X3 x)) (M.op X4 (M.op (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) X4))) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e81 (M.op X0 x) X1 X2 X3 X4
             have i₂ := b2e26066 X0 (M.op (M.op X1 (M.op X2 X3)) (M.op X0 x))
             grind)
          | exact superpose b2e26066 b2e81
          | exact resolve b2e81 b2e26066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e27835 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y X4) (M.op (M.op X3 x) (M.op (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) X4))) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e27749 X0 X1 X2 X3 X4
             have i₂ := b2e26889 X4 (M.op X3 x) (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x)))
             grind)
          | exact superpose b2e26889 b2e27749
          | exact resolve b2e27749 b2e26889
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26889 b2e27749
        have b2e27896 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y X4) (M.op y (M.op (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) X4))) = X4 := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e27835 X0 X1 X2 X3 X4
             have i₂ := b2e26066 X3 (M.op (M.op y (M.op (M.op X0 (M.op X1 X2)) (M.op X3 x))) X4)
             grind)
          | exact superpose b2e26066 b2e27835
          | exact resolve b2e27835 b2e26066
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26066 b2e27835
        have b2e27913 : ∀ X4 : G, (M.op (M.op y X4) (M.op y (M.op x X4))) = X4 := by
          intro X4
          first
          | (have i₁ := b2e27896 x x x x X4
             have i₂ := b2e26483 y (M.op x (M.op x x)) x x X4
             grind)
          | exact superpose b2e26483 b2e27896
          | exact resolve b2e27896 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27896
        have b2e32343 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X0)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26086 X2 (M.op (M.op X0 (M.op X1 X0)) X0) X3 (M.op (M.op X1 (M.op (M.op x x) X1)) (M.op (M.op x x) (M.op X1 (M.op (M.op x x) X1))))
             have i₂ := b2e86 X0 X1 x x x x
             grind)
          | exact superpose b2e86 b2e26086
          | exact resolve b2e26086 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32402 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) X1) = (M.op (M.op X0 (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e26086 X0 (σ y) X1 (σ x)
             have i₂ := b2e141
             grind)
          | exact superpose b2e141 b2e26086
          | exact resolve b2e26086 b2e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e33156 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X4 X2)) (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1)))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e94 X2 X4 (M.op X3 X1)
             have i₂ := b2e26086 X3 X1 (M.op X2 (M.op X3 X1)) X0
             grind)
          | (have i₁ := b2e94 X2 X4 (M.op X3 X1)
             have i₂ := b2e26086 X0 X1 (M.op X2 (M.op X3 X1)) X3
             grind)
          | exact superpose b2e26086 b2e94
          | exact resolve b2e94 b2e26086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e35490 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op X0 (M.op (M.op y (M.op x X0)) X0)) := by
          intro X0
          first
          | (have i₁ := b2e12 (M.op y (M.op x X0)) X0 y
             have i₂ := b2e27913 X0
             grind)
          | exact superpose b2e27913 b2e12
          | exact resolve b2e12 b2e27913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35508 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op x X0))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e26086 X1 X0 (M.op y (M.op x X0)) y
             have i₂ := b2e27913 X0
             grind)
          | exact superpose b2e27913 b2e26086
          | exact resolve b2e26086 b2e27913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37996 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x X0)) X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op (M.op y (M.op x X0)) X0) (M.op y (M.op x X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e201 (M.op X1 X0) (M.op y (M.op x X0)) X2
             have i₂ := b2e35508 X0 X1
             grind)
          | exact superpose b2e35508 b2e201
          | exact resolve b2e201 b2e35508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e201
        have b2e38024 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X0) = (M.op (M.op y (M.op x X0)) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e37996 X0 X1 X2
             have i₂ := b2e35508 X0 (M.op y (M.op x X0))
             grind)
          | exact superpose b2e35508 b2e37996
          | exact resolve b2e37996 b2e35508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37996
        have b2e45819 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X1) = (M.op (M.op y (M.op x X0)) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26483 X2 X3 (M.op y X0) (M.op y (M.op x X0)) X1
             have i₂ := b2e27913 X0
             grind)
          | exact superpose b2e27913 b2e26483
          | exact resolve b2e26483 b2e27913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27913
        have b2e45904 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) X1) = (M.op (M.op X0 (M.op y X0)) X1) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e26483 X2 X3 x (M.op X0 (M.op y X0)) X1
             have i₂ := b2e26 X0
             grind)
          | exact superpose b2e26 b2e26483
          | exact resolve b2e26483 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e46374 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X0))))) X1)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X0))))) X1)) X1)) := by
          intro X0 X1 X2 X3 X4 X5 X6
          first
          | (have i₁ := b2e28 X1 (M.op X4 (M.op X5 (M.op X6 X0))) X2 X3
             have i₂ := b2e26483 X4 X5 X6 X0 (M.op (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X0))))) X1)) X1)
             grind)
          | exact superpose b2e26483 b2e28
          | exact resolve b2e28 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e46464 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X0 (M.op (M.op y (M.op x X1)) X1)) = (M.op X1 (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X0))))) X1)) := by
          intro X0 X1 X2 X3 X4 X5 X6
          first
          | (have i₁ := b2e46374 X0 X1 X2 X3 X4 X5 X6
             have i₂ := b2e38024 X1 (M.op X2 (M.op X3 (M.op X4 (M.op X5 (M.op X6 X0))))) X1
             grind)
          | exact superpose b2e38024 b2e46374
          | exact resolve b2e46374 b2e38024
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38024 b2e46374
        have b2e46640 : ∀ X0 X1 X5 X6 : G, (M.op X0 (M.op (M.op y (M.op x X1)) X1)) = (M.op X1 (M.op (M.op X5 (M.op X6 X0)) X1)) := by
          intro X0 X1 X5 X6
          first
          | (have i₁ := b2e46464 X0 X1 x x x X5 X6
             have i₂ := b2e26483 x x x (M.op X5 (M.op X6 X0)) X1
             grind)
          | exact superpose b2e26483 b2e46464
          | exact resolve b2e46464 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46464
        have b2e49904 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X6 X7) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1 X2 X3 X6 X7
          first
          | (have i₁ := b2e219 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x) (M.op X1 (M.op (M.op X2 X3) X1)) x x
             have i₂ := b2e86 X0 X1 X2 X3 x x
             grind)
          | exact superpose b2e86 b2e219
          | exact resolve b2e219 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e50062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e28 (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) X3 X3 (M.op x x)
             have i₂ := b2e219 X0 X1 X2 X3 x x
             grind)
          | exact superpose b2e219 b2e28
          | exact resolve b2e28 b2e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e219
        have b2e50268 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e50062 X0 X1 X2 X3
             have i₂ := b2e32343 X0 (M.op X1 (M.op X2 X3)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))
             grind)
          | exact superpose b2e32343 b2e50062
          | exact resolve b2e50062 b2e32343
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50062
        have b2e50391 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op y (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e49904 X0 X1 X2 X3 x x
             have i₂ := b2e45904 (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x)
             grind)
          | exact superpose b2e45904 b2e49904
          | exact resolve b2e49904 b2e45904
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49904
        have b2e50724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e50268 X0 X1 X2 X3
             have i₂ := b2e33156 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0 X0 (M.op X1 (M.op X2 X3)) (M.op X1 (M.op X2 X3))
             grind)
          | exact superpose b2e33156 b2e50268
          | exact resolve b2e50268 b2e33156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50268
        have b2e50829 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y (M.op x (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e50391 X0 X1 X2 X3
             have i₂ := b2e45819 (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))) (M.op X1 (M.op (M.op X2 X3) X1)) y
             grind)
          | exact superpose b2e45819 b2e50391
          | exact resolve b2e50391 b2e45819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50391
        have b2e51138 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 (M.op X2 X3)) X0) (M.op y (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e50724 X0 X1 X2 X3
             have i₂ := b2e45904 (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) X0
             grind)
          | exact superpose b2e45904 b2e50724
          | exact resolve b2e50724 b2e45904
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50724
        have b2e51234 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e50829 X0 X1 X2 X3
             have i₂ := b2e26483 y x X1 (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
             grind)
          | exact superpose b2e26483 b2e50829
          | exact resolve b2e50829 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50829
        have b2e51486 : ∀ X0 X1 X2 X3 : G, (M.op (M.op y (M.op x (M.op (M.op X1 (M.op X2 X3)) X0))) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e51138 X0 X1 X2 X3
             have i₂ := b2e45819 (M.op (M.op X1 (M.op X2 X3)) X0) (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op (M.op X1 (M.op X2 X3)) X0) y
             grind)
          | exact superpose b2e45819 b2e51138
          | exact resolve b2e51138 b2e45819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51138
        have b2e51562 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1
          first
          | (have i₁ := b2e51234 X0 X1 x x
             have i₂ := b2e24757 X1 (M.op x x) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
             grind)
          | exact superpose b2e24757 b2e51234
          | exact resolve b2e51234 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51234
        have b2e51709 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e51486 X0 X1 X2 X3
             have i₂ := b2e26483 y x (M.op X1 (M.op X2 X3)) X0 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)
             grind)
          | exact superpose b2e26483 b2e51486
          | exact resolve b2e51486 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51486
        have b2e51770 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
          intro X0 X1
          first
          | (have i₁ := b2e51562 X0 X1
             have i₂ := b2e32343 X0 X1 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))
             grind)
          | exact superpose b2e32343 b2e51562
          | exact resolve b2e51562 b2e32343
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32343 b2e51562
        have b2e51903 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op y (M.op x X0)) X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e51709 X0 X1 X2 X3
             have i₂ := b2e46640 X0 X0 X0 (M.op X1 (M.op X2 X3))
             grind)
          | exact superpose b2e46640 b2e51709
          | exact resolve b2e51709 b2e46640
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46640 b2e51709
        have b2e51946 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e51770 X0 X1
             have i₂ := b2e33156 (M.op X0 (M.op X1 X0)) X0 X0 X1 X1
             grind)
          | exact superpose b2e33156 b2e51770
          | exact resolve b2e51770 b2e33156
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33156 b2e51770
        have b2e52034 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op x X0)) = (M.op X3 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e51903 X0 X1 X2 X3
             have i₂ := b2e35490 X0
             grind)
          | exact superpose b2e35490 b2e51903
          | exact resolve b2e51903 b2e35490
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35490 b2e51903
        have b2e52066 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op y (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e51946 X0 X1
             have i₂ := b2e45904 (M.op X1 X0) (M.op (M.op X0 (M.op X1 X0)) X0) (M.op (M.op X0 (M.op X1 X0)) X0) X0
             grind)
          | exact superpose b2e45904 b2e51946
          | exact resolve b2e51946 b2e45904
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45904 b2e51946
        have b2e52137 : ∀ X0 X1 : G, (M.op (M.op y X1) (M.op X1 X0)) = (M.op (M.op y (M.op x (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e52066 X0 X1
             have i₂ := b2e45819 (M.op X1 X0) (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X1 X0) y
             grind)
          | exact superpose b2e45819 b2e52066
          | exact resolve b2e52066 b2e45819
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45819 b2e52066
        have b2e52172 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e52137 X0 X1
             have i₂ := b2e26483 y x X1 X0 (M.op (M.op X0 (M.op X1 X0)) X0)
             grind)
          | exact superpose b2e26483 b2e52137
          | exact resolve b2e52137 b2e26483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26483 b2e52137
        have b2e52192 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e52172 X0 X1
             have i₂ := b2e52034 X0 X0 X1 X0
             grind)
          | exact superpose b2e52034 b2e52172
          | exact resolve b2e52172 b2e52034
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52034 b2e52172
        have b2e52500 : ∀ X0 X1 X2 : G, (M.op y (M.op x X0)) = (M.op (M.op X1 X2) (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e26086 X1 X2 (M.op X2 X0) y
             have i₂ := b2e52192 X0 X2
             grind)
          | exact superpose b2e52192 b2e26086
          | exact resolve b2e26086 b2e52192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26086 b2e52192
        have b2e128352 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8301 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e8301
          | exact resolve b2e8301 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8301
        have b2e128492 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e128352 X0
             have i₂ := b2e25 X0 (τ X0)
             grind)
          | exact superpose b2e25 b2e128352
          | (have j0 := b2e128352 X0
             grind)
          | exact resolve b2e128352 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e128352
        have b2e128513 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e128492 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e128492
          | (have j0 := b2e128492 X0
             grind)
          | exact resolve b2e128492 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128492
        have b2e128518 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e128513 X0
             have j1 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e128513 X0
             have r₂ := b2e15 X0 X0
             grind)
          | exact resolve b2e128513 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128513
        have b2e128551 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e128518 (σ X0)
             grind)
          | exact superpose b2e128518 b2e18
          | exact resolve b2e18 b2e128518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e128574 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e128551 X0
             have i₂ := b2e128518 X0
             grind)
          | exact superpose b2e128518 b2e128551
          | exact resolve b2e128551 b2e128518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128518 b2e128551
        have b2e129460 : (σ y) = (M.op (M.op (σ x) (σ (M.op x x))) (M.op (σ y) (σ (M.op x x)))) := by
          first
          | (have i₁ := b2e564 (σ x)
             have i₂ := b2e128574 x
             grind)
          | exact superpose b2e128574 b2e564
          | exact resolve b2e564 b2e128574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e564
        have b2e129468 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (M.op (σ (M.op X0 X0)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 (σ X0) (σ X0)
             have i₂ := b2e128574 X0
             grind)
          | exact superpose b2e128574 b2e12
          | exact resolve b2e12 b2e128574
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e129594 : (σ y) = (M.op (M.op y (σ (M.op x x))) (M.op (σ y) (σ (M.op x x)))) := by
          first
          | (have i₁ := b2e129460
             have i₂ := b2e24757 (σ (M.op x x)) (σ x) (M.op (σ y) (σ (M.op x x)))
             grind)
          | exact superpose b2e24757 b2e129460
          | exact resolve b2e129460 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129460
        have b2e134095 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (M.op (M.op X0 (σ y)) X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e129468 x X1
             have i₂ := b2e32402 X0 X1
             grind)
          | exact superpose b2e32402 b2e129468
          | exact resolve b2e129468 b2e32402
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32402 b2e129468
        have b2e136018 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op (M.op (σ y) X0) (M.op y (M.op x X0)))) := by
          intro X0
          first
          | (have i₁ := b2e134095 x (M.op (σ y) X0)
             have i₂ := b2e52500 X0 x (σ y)
             grind)
          | exact superpose b2e52500 b2e134095
          | exact resolve b2e134095 b2e52500
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52500 b2e134095
        have b2e136199 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e136018 X0
             have i₂ := b2e35508 X0 (σ y)
             grind)
          | exact superpose b2e35508 b2e136018
          | exact resolve b2e136018 b2e35508
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35508 b2e136018
        have b2e136417 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e128574 x
             have i₂ := b2e136199 (σ x)
             grind)
          | exact superpose b2e136199 b2e128574
          | exact resolve b2e128574 b2e136199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128574
        have b2e136614 : (σ x) = (M.op (M.op (σ y) (σ (M.op x x))) (M.op (σ y) (M.op (σ y) (σ x)))) := by
          first
          | (have i₁ := b2e537 (σ x)
             have i₂ := b2e136199 (M.op (σ y) (σ x))
             grind)
          | exact superpose b2e136199 b2e537
          | exact resolve b2e537 b2e136199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e537 b2e136199
        have b2e136719 : (σ x) = (M.op (M.op y (σ (M.op x x))) (M.op (σ y) (M.op (σ y) (σ x)))) := by
          first
          | (have i₁ := b2e136614
             have i₂ := b2e24757 (σ (M.op x x)) (σ y) (M.op (σ y) (M.op (σ y) (σ x)))
             grind)
          | exact superpose b2e24757 b2e136614
          | exact resolve b2e136614 b2e24757
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24757 b2e136614
        have b2e136827 : (σ x) = (M.op (M.op y (σ (M.op x x))) (M.op (σ y) (σ (M.op x x)))) := by
          first
          | (have i₁ := b2e136719
             have i₂ := b2e136417
             grind)
          | exact superpose b2e136417 b2e136719
          | exact resolve b2e136719 b2e136417
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136417 b2e136719
        have b2e136873 : (σ x) = (σ y) := by
          first
          | (have i₁ := b2e136827
             have i₂ := b2e129594
             grind)
          | exact superpose b2e129594 b2e136827
          | exact resolve b2e136827 b2e129594
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e129594 b2e136827
        have b2e137042 : x = (τ (σ y)) := by
          first
          | (have i₁ := b2e13 x
             have i₂ := b2e136873
             grind)
          | exact superpose b2e136873 b2e13
          | exact resolve b2e13 b2e136873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136873
        have b2e137163 : x = y := by
          first
          | (have i₁ := b2e137042
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e137042
          | exact resolve b2e137042 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e137042
        have b2e137364 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e142
             have i₂ := b2e137163
             grind)
          | exact superpose b2e137163 b2e142
          | exact resolve b2e142 b2e137163
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e142 b2e137163
        have b2e137481 : False := by grind
        exact b2e137481
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e26 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
             have i₂ := b3e12 X0 X2 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e36 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e34
        have b3e37 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e36
          | exact resolve b3e36 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e40 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e43 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X2 X1) X0)) ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X2 X1) X1 X2
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X2 X1) X0)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 (M.op X2 X1) X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b3e49 : y = (k x y) ∨ y = (M.op y x) := by grind
        have b3e50 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e51 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
          intro X0
          grind
        clear b3e24
        have b3e52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e53 : y = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e20
             grind)
          | exact resolve b3e49 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e68 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e15
          | exact resolve b3e15 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e71 : (σ x) ≠ (σ y) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e68
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e68
          | exact resolve b3e68 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e75 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e71
          | exact resolve b3e71 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e77 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b3e75
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e75
          | exact resolve b3e75 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e110 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e28 x X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e28
          | exact resolve b3e28 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e117 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
             have i₂ := b3e28 X1 x x X0
             grind)
          | exact superpose b3e28 b3e12
          | exact resolve b3e12 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e308 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40 x x
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e40
          | exact resolve b3e40 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e363 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
        clear b3e308
        have b3e380 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e363
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e363
          | exact resolve b3e363 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e363
        have b3e395 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e380
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e380
          | exact resolve b3e380 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e380
        have b3e400 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b3e395
             have r₂ := b3e77
             grind)
          | exact resolve b3e395 b3e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77 b3e395
        have b3e405 : (k x x) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e400
             grind)
          | exact superpose b3e400 b3e13
          | exact resolve b3e13 b3e400
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e400
        have b3e420 : y = (k x x) := by
          first
          | (have i₁ := b3e405
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e405
          | exact resolve b3e405 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e405
        have b3e507 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X1 X0
             have i₂ := b3e43 X1 X1 X0
             grind)
          | exact superpose b3e43 b3e12
          | (have j1 := b3e43 X1 X1 X0
             grind)
          | exact resolve b3e12 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e526 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e507 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e507
        have b3e593 : ∀ X0 : G, x = (M.op (M.op x (M.op X0 x)) (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e110 x (M.op X0 (M.op y X0))
             have i₂ := b3e26 X0
             grind)
          | exact superpose b3e26 b3e110
          | exact resolve b3e110 b3e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e110
        have b3e942 : x = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b3e593 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e593
          | exact resolve b3e593 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e593
        have b3e1892 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e526 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e526
          | exact resolve b3e526 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e526
        have b3e1914 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e1892
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e1892
          | exact resolve b3e1892 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1892
        have b3e1922 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e1914
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1914
          | exact resolve b3e1914 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1914
        have b3e13163 : ∀ X0 : G, (k (τ X0) (M.op (τ X0) (τ X0))) = (τ (σ (M.op (τ X0) (τ X0)))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b3e48 X0 (M.op (τ X0) (τ X0))
             have i₂ := b3e51 X0
             grind)
          | exact superpose b3e51 b3e48
          | (have j1 := b3e51 X0
             grind)
          | exact resolve b3e48 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e13192 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) ∨ (M.op (τ X0) (τ X0)) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
          intro X0
          first
          | (have i₁ := b3e13163 X0
             have i₂ := b3e13 (M.op (τ X0) (τ X0))
             grind)
          | exact superpose b3e13 b3e13163
          | (have j0 := b3e13163 X0
             grind)
          | exact resolve b3e13163 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13163
        have b3e13218 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
          intro X0
          first
          | (have j0 := b3e13192 X0
             have j1 := b3e15 (τ X0) (M.op (τ X0) (τ X0))
             grind)
          | (have r₁ := b3e13192 X0
             have r₂ := b3e15 (τ X0) (M.op (τ X0) (τ X0))
             grind)
          | exact resolve b3e13192 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13192
        have b3e14882 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e13218 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e13218
          | exact resolve b3e13218 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e13218
        have b3e15073 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e14882 (M.op x (M.op x x))
             have i₂ := b3e117 x x x
             grind)
          | exact superpose b3e117 b3e14882
          | exact resolve b3e14882 b3e117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e117
        have b3e15084 : x = (k (M.op x y) x) := by
          first
          | (have i₁ := b3e14882 (M.op x y)
             have i₂ := b3e942
             grind)
          | exact superpose b3e942 b3e14882
          | exact resolve b3e14882 b3e942
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e942 b3e14882
        have b3e15728 : (σ x) = (k (M.op (σ x) (σ (k x y))) (σ x)) := by
          first
          | (have i₁ := b3e15073 (σ x)
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e15073
          | exact resolve b3e15073 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37 b3e15073
        have b3e15762 : (σ x) = (k (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b3e15728
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e15728
          | exact resolve b3e15728 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e15728
        have b3e16091 : (τ (σ x)) = (k (τ (M.op (σ x) (σ y))) x) := by
          first
          | (have i₁ := b3e48 (M.op (σ x) (σ y)) x
             have i₂ := b3e15762
             grind)
          | exact superpose b3e15762 b3e48
          | exact resolve b3e48 b3e15762
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e15762
        have b3e16095 : x = (k (τ (M.op (σ x) (σ y))) x) := by
          first
          | (have i₁ := b3e16091
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e16091
          | exact resolve b3e16091 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e16091
        have b3e128128 : x = (k (τ (σ x)) x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e16095
             have i₂ := b3e1922
             grind)
          | exact superpose b3e1922 b3e16095
          | exact resolve b3e16095 b3e1922
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1922 b3e16095
        have b3e128261 : x = (k x x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b3e128128
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e128128
          | exact resolve b3e128128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128128
        have b3e128294 : (σ y) = (σ (k y x)) ∨ x = y := by
          first
          | (have i₁ := b3e128261
             have i₂ := b3e420
             grind)
          | exact superpose b3e420 b3e128261
          | exact resolve b3e128261 b3e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128261
        have b3e128353 : (k y x) = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e128294
             grind)
          | exact superpose b3e128294 b3e13
          | exact resolve b3e13 b3e128294
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128294
        have b3e128426 : y = (k y x) ∨ x = y := by
          first
          | (have i₁ := b3e128353
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e128353
          | exact resolve b3e128353 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128353
        have b3e128624 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b3e52 x y
             have i₂ := b3e128426
             grind)
          | exact superpose b3e128426 b3e52
          | (have j0 := b3e52 y x
             grind)
          | exact resolve b3e52 b3e128426
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e128426
        have b3e128628 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by grind
        clear b3e128624
        have b3e128629 : x = (M.op x y) ∨ x = y := by
          first
          | (have r₁ := b3e128628
             have r₂ := b3e20
             grind)
          | exact resolve b3e128628 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128628
        have b3e130078 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b3e15084
             have i₂ := b3e128629
             grind)
          | exact superpose b3e128629 b3e15084
          | exact resolve b3e15084 b3e128629
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e15084 b3e128629
        have b3e130288 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e130078
             have i₂ := b3e420
             grind)
          | exact superpose b3e420 b3e130078
          | exact resolve b3e130078 b3e420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e420 b3e130078
        have b3e130289 : x = y := by grind
        clear b3e130288
        have b3e131150 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e130289
             grind)
          | exact superpose b3e130289 b3e20
          | exact resolve b3e20 b3e130289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e131151 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e130289
             grind)
          | exact superpose b3e130289 b3e21
          | exact resolve b3e21 b3e130289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130289
        have b3e131392 : False := by grind
        exact b3e131392
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b4e26
          have b4e32 : ∀ X0 : G, (M.op x (M.op X0 (M.op y X0))) = X0 := by
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
          have b4e33 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = X0 := by
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
          have b4e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X0)) (M.op X3 (M.op X0 X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X0 (M.op (M.op X1 X2) X0)) X2
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) = (M.op X1 (M.op (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X0 (M.op (M.op X2 (M.op X3 X1)) X0)) X1 X3
               have i₂ := b4e13 X0 (M.op X3 X1) X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op X1 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 (M.op y X0)) x
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e18 (σ X0) (σ X1)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (σ y)) X0)) = (M.op (σ x) (M.op (M.op X0 (M.op (M.op X1 (σ y)) X0)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (M.op X0 (M.op (M.op X1 (σ y)) X0))
               have i₂ := b4e13 X0 (σ y) X1
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e75 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31
            | exact resolve b4e31 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e105 : ∀ X0 X1 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X4 (M.op (M.op X0 (M.op X1 X0)) X4))) = X4 := by
            intro X0 X1 X4
            first
            | (have i₁ := b4e34 (M.op X0 (M.op X1 X0)) X1 (M.op (M.op x x) X1) X4
               have i₂ := b4e34 X1 x x X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X4 X5) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e34 (M.op X1 (M.op (M.op X2 X3) X1)) X4 X5 (M.op X0 (M.op X1 X0))
               have i₂ := b4e34 X1 X2 X3 X0
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e114 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 x X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e34
            | exact resolve b4e34 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e115 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x (M.op (M.op X1 X2) x)) (M.op (M.op X0 (M.op y X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 x X1 X2 (M.op X0 (M.op y X0))
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e34
            | exact resolve b4e34 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X2 (M.op X0 X2))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op X0 (M.op X1 X0)) (M.op X1 (M.op (M.op x x) X1))
               have i₂ := b4e34 X1 x x X0
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e275 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) (M.op (M.op X1 (M.op X0 X1)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e35 X0 (M.op (σ y) X0) (σ x) X0
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e35
            | exact resolve b4e35 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e290 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op (M.op X1 (M.op X2 X0)) X0) X0
               have i₂ := b4e35 X0 X0 X1 X2
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e293 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e34 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3 X4 X0
               have i₂ := b4e35 X0 X0 X1 X2
               grind)
            | exact superpose b4e35 b4e34
            | exact resolve b4e34 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e301 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) = (M.op (M.op X3 (M.op (M.op X4 X5) X3)) (M.op (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e34 X3 X4 X5 (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X0)) X0)
               have i₂ := b4e35 X0 X3 X1 X2
               grind)
            | exact superpose b4e35 b4e34
            | exact resolve b4e34 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e385 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X1) (σ X0)
               have i₂ := b4e46 X1 X0
               grind)
            | exact superpose b4e46 b4e16
            | (have j0 := b4e16 (σ X1) (σ X0)
               have j1 := b4e46 X1 X0
               grind)
            | (have r₁ := b4e16 (σ X1) (σ X1)
               have r₂ := b4e46 X1 X1
               grind)
            | (have r₁ := b4e16 (σ X0) (σ X1)
               have r₂ := b4e46 X0 X1
               grind)
            | exact resolve b4e16 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e395 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e385 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e385
          have b4e408 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e395 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e395
            | (have j0 := b4e395 X0 X1
               grind)
            | exact resolve b4e395 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e395
          have b4e1764 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X0) = (M.op (M.op X0 (M.op X2 X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e121 X0 X1 (M.op (M.op X0 (M.op X2 X0)) X0)
               have i₂ := b4e105 X0 X2 X0
               grind)
            | exact superpose b4e105 b4e121
            | exact resolve b4e121 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e2301 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e275 X0 (M.op (M.op X1 (M.op X2 X0)) X0)
               have i₂ := b4e290 X0 X1 X2
               grind)
            | exact superpose b4e290 b4e275
            | exact resolve b4e275 b4e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2304 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) (M.op X0 X1)) X1 X0
               have i₂ := b4e290 (M.op X0 X1) X2 X3
               grind)
            | exact superpose b4e290 b4e13
            | exact resolve b4e13 b4e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2312 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 (M.op X1 y)) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 (M.op (M.op X0 (M.op X1 y)) y)
               have i₂ := b4e290 y X0 X1
               grind)
            | exact superpose b4e290 b4e32
            | exact resolve b4e32 b4e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2640 : ∀ X0 X1 : G, (M.op y (M.op y y)) = (M.op (M.op x (M.op (M.op X0 X1) x)) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e115 y X0 X1
               have i₂ := b4e2312 y y
               grind)
            | exact superpose b4e2312 b4e115
            | exact resolve b4e115 b4e2312
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115 b4e2312
          have b4e2710 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b4e2640 x x
               have i₂ := b4e114 x x
               grind)
            | exact superpose b4e114 b4e2640
            | exact resolve b4e2640 b4e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e114 b4e2640
          have b4e9072 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e408 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e408
          have b4e9074 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e9072 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9072
          have b4e23048 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X0)) = (M.op (M.op (σ y) X2) (M.op (M.op X0 (M.op X1 X0)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e275 X2 X0
               have i₂ := b4e1764 X0 X2 X1
               grind)
            | (have i₁ := b4e275 X2 X0
               have i₂ := b4e1764 X0 X1 X2
               grind)
            | exact superpose b4e1764 b4e275
            | exact resolve b4e275 b4e1764
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1764
          have b4e27052 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (M.op X4 X5)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e35 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X5 X3 X4
               have i₂ := b4e293 X0 X1 X2 X3 (M.op X4 X5)
               grind)
            | exact superpose b4e293 b4e35
            | exact resolve b4e35 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27053 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 (σ y)) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e71 (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) X3
               have i₂ := b4e293 X0 X1 X2 X3 (σ y)
               grind)
            | exact superpose b4e293 b4e71
            | exact resolve b4e71 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e27062 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) (M.op (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)))) = (M.op (M.op (σ y) (M.op X3 X4)) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e275 (M.op X3 X4) (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0))
               have i₂ := b4e293 X0 X1 X2 X3 X4
               grind)
            | exact superpose b4e293 b4e275
            | exact resolve b4e275 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293
          have b4e27181 : ∀ X0 X3 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op X3 (σ y))) X0) := by
            intro X0 X3
            first
            | (have i₁ := b4e27053 X0 x x X3
               have i₂ := b4e27062 X0 x x X3 (σ y)
               grind)
            | exact superpose b4e27062 b4e27053
            | exact resolve b4e27053 b4e27062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27053
          have b4e27182 : ∀ X0 X3 X4 X5 : G, (M.op X5 X0) = (M.op (M.op (σ y) (M.op X3 (M.op X4 X5))) X0) := by
            intro X0 X3 X4 X5
            first
            | (have i₁ := b4e27052 X0 x x X3 X4 X5
               have i₂ := b4e27062 X0 x x X3 (M.op X4 X5)
               grind)
            | exact superpose b4e27062 b4e27052
            | exact resolve b4e27052 b4e27062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27052 b4e27062
          have b4e31564 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (M.op X0 (M.op (σ x) X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 (σ y)) (σ y)
               have i₂ := b4e27181 X0 X1
               grind)
            | exact superpose b4e27181 b4e13
            | exact resolve b4e13 b4e27181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27181
          have b4e34820 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e31564 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e31564
            | exact resolve b4e31564 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31564
          have b4e37672 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (σ y) X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e27182 X2 (M.op X1 (M.op y X1)) X0 (M.op X1 X0)
               have i₂ := b4e37 X1 X0
               grind)
            | exact superpose b4e37 b4e27182
            | exact resolve b4e27182 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e37731 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e27182 X1 x X0 (M.op y X0)
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e27182
            | exact resolve b4e27182 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e37748 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (σ y) x) X0) := by
            intro X0
            first
            | (have i₁ := b4e27182 X0 y y y
               have i₂ := b4e2710
               grind)
            | exact superpose b4e2710 b4e27182
            | exact resolve b4e27182 b4e2710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2710
          have b4e43931 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e37672 X1 X0 X2
               have i₂ := b4e37672 X1 X3 X2
               grind)
            | (have i₁ := b4e37672 X0 X1 X2
               have i₂ := b4e37672 X0 (σ y) X2
               grind)
            | exact superpose b4e37672 b4e37672
            | exact resolve b4e37672 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44361 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e37748 X1
               have i₂ := b4e37672 x X0 X1
               grind)
            | (have i₁ := b4e37748 x
               have i₂ := b4e37672 x (σ y) x
               grind)
            | exact superpose b4e37672 b4e37748
            | exact resolve b4e37748 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37748
          have b4e44423 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op (M.op (σ y) (M.op (σ y) X1)) (M.op (M.op X2 (M.op (M.op X0 X1) X2)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e275 (M.op X1 X0) X2
               have i₂ := b4e37672 X0 X1 X2
               grind)
            | (have i₁ := b4e275 (M.op (σ y) X0) X2
               have i₂ := b4e37672 X0 X1 X2
               grind)
            | exact superpose b4e37672 b4e275
            | exact resolve b4e275 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e275
          have b4e44468 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X4) = (M.op (M.op X0 (M.op X1 (M.op X2 X3))) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e27182 X4 X1 X2 X3
               have i₂ := b4e37672 (M.op X1 (M.op X2 X3)) X0 X4
               grind)
            | (have i₁ := b4e27182 X2 X3 X4 x
               have i₂ := b4e37672 (M.op X3 (M.op X4 x)) (σ y) X2
               grind)
            | exact superpose b4e37672 b4e27182
            | exact resolve b4e27182 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27182
          have b4e44731 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op (M.op (σ y) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e44423 X0 X1 X2
               have i₂ := b4e23048 X2 (M.op X0 X1) (M.op (σ y) X1)
               grind)
            | exact superpose b4e23048 b4e44423
            | exact resolve b4e44423 b4e23048
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23048 b4e44423
          have b4e45023 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X2)) = (M.op X2 (M.op (M.op y X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e44731 X0 X1 X2
               have i₂ := b4e37731 X1 X2
               grind)
            | exact superpose b4e37731 b4e44731
            | exact resolve b4e44731 b4e37731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44731
          have b4e47165 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 (M.op (M.op X1 (M.op X2 x)) X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op X2 x) X1
               have i₂ := b4e44361 X2 (M.op X0 (M.op (M.op X1 (M.op X2 x)) X0))
               grind)
            | exact superpose b4e44361 b4e13
            | exact resolve b4e13 b4e44361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44361
          have b4e48825 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 (M.op (M.op X0 (M.op X1 X0)) X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e43931 X2 (M.op (M.op X0 (M.op X1 X0)) X0) X3 (M.op (M.op X1 (M.op (M.op x x) X1)) (M.op (M.op x x) (M.op X1 (M.op (M.op x x) X1))))
               have i₂ := b4e111 X0 X1 x x x x
               grind)
            | exact superpose b4e111 b4e43931
            | exact resolve b4e43931 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49706 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X1) = (M.op (M.op X2 (M.op X4 X2)) (M.op (M.op X0 X1) (M.op X2 (M.op X3 X1)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e121 X2 X4 (M.op X3 X1)
               have i₂ := b4e43931 X3 X1 (M.op X2 (M.op X3 X1)) X0
               grind)
            | (have i₁ := b4e121 X2 X4 (M.op X3 X1)
               have i₂ := b4e43931 X0 X1 (M.op X2 (M.op X3 X1)) X3
               grind)
            | exact superpose b4e43931 b4e121
            | exact resolve b4e121 b4e43931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e49753 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) = (M.op X4 (M.op (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) (M.op X5 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e35 (M.op X0 X1) X1 X2 X3
               have i₂ := b4e43931 X0 X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X0 X1)) X3
               grind)
            | (have i₁ := b4e35 (M.op X3 X1) X1 X2 X3
               have i₂ := b4e43931 X0 X1 (M.op (M.op X2 (M.op X3 X1)) (M.op X3 X1)) X3
               grind)
            | exact superpose b4e43931 b4e35
            | exact resolve b4e35 b4e43931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e49905 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op (M.op X2 (M.op X3 X4)) (M.op X5 X1))) = (M.op X4 (M.op X1 (M.op X5 X1))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e49753 X0 X1 X2 X3 X4 X5
               have i₂ := b4e2304 X5 X1 (M.op X0 X1) (M.op X2 (M.op X3 X4))
               grind)
            | exact superpose b4e2304 b4e49753
            | exact resolve b4e49753 b4e2304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2304 b4e49753
          have b4e54082 : ∀ X0 X1 X2 X3 X6 X7 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X1 (M.op (M.op X2 X3) X1)) (M.op (M.op X6 X7) (M.op X1 (M.op (M.op X2 X3) X1)))) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1 X2 X3 X6 X7
            first
            | (have i₁ := b4e301 (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x) (M.op X1 (M.op (M.op X2 X3) X1)) x x
               have i₂ := b4e111 X0 X1 X2 X3 x x
               grind)
            | exact superpose b4e111 b4e301
            | exact resolve b4e301 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111 b4e301
          have b4e54575 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e54082 X0 X1 X2 X3 x x
               have i₂ := b4e44468 (M.op X1 (M.op (M.op X2 X3) X1)) (M.op x x) X1 (M.op (M.op X2 X3) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
               grind)
            | exact superpose b4e44468 b4e54082
            | exact resolve b4e54082 b4e44468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54082
          have b4e55070 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op (σ y) X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e54575 X0 X1 x x
               have i₂ := b4e37672 X1 (M.op x x) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
               grind)
            | exact superpose b4e37672 b4e54575
            | exact resolve b4e54575 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54575
          have b4e55354 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e55070 X0 X1
               have i₂ := b4e37731 X1 (M.op (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))
               grind)
            | exact superpose b4e37731 b4e55070
            | exact resolve b4e55070 b4e37731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55070
          have b4e55574 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e55354 X0 X1
               have i₂ := b4e48825 X0 X1 (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0)))
               grind)
            | exact superpose b4e48825 b4e55354
            | exact resolve b4e55354 b4e48825
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48825 b4e55354
          have b4e55724 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op y X0) (M.op X0 (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b4e55574 X0 X1
               have i₂ := b4e45023 (M.op X0 (M.op X1 X0)) X0 (M.op X0 (M.op X1 X0))
               grind)
            | exact superpose b4e45023 b4e55574
            | exact resolve b4e55574 b4e45023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45023 b4e55574
          have b4e55823 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 (M.op X1 X0)) X0) (M.op X0 (M.op X1 X0))) (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e55724 X0 X1
               have i₂ := b4e49706 y X0 X0 X1 X1
               grind)
            | exact superpose b4e49706 b4e55724
            | exact resolve b4e55724 b4e49706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49706 b4e55724
          have b4e55883 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e55823 X0 X1
               have i₂ := b4e44468 (M.op (M.op X0 (M.op X1 X0)) X0) X0 X1 X0 (M.op (M.op X0 (M.op X1 X0)) X0)
               grind)
            | exact superpose b4e44468 b4e55823
            | exact resolve b4e55823 b4e44468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44468 b4e55823
          have b4e86993 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op y (M.op (M.op (σ y) X0) (M.op (M.op X1 (M.op X2 x)) (M.op X3 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e47165 (M.op X3 X0) X1 X2
               have i₂ := b4e37672 X0 X3 (M.op (M.op X1 (M.op X2 x)) (M.op X3 X0))
               grind)
            | (have i₁ := b4e47165 (M.op (σ y) X0) X1 X2
               have i₂ := b4e37672 X0 X1 (M.op (M.op X1 (M.op X2 x)) (M.op (σ y) X0))
               grind)
            | exact superpose b4e37672 b4e47165
            | exact resolve b4e47165 b4e37672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37672 b4e47165
          have b4e87134 : ∀ X0 X3 : G, (M.op X3 X0) = (M.op y (M.op x (M.op X0 (M.op X3 X0)))) := by
            intro X0 X3
            first
            | (have i₁ := b4e86993 X0 x x X3
               have i₂ := b4e49905 (σ y) X0 x x x X3
               grind)
            | exact superpose b4e49905 b4e86993
            | exact resolve b4e86993 b4e49905
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49905 b4e86993
          have b4e93834 : (σ y) = (M.op y (M.op x (M.op (σ x) (σ y)))) := by
            first
            | (have i₁ := b4e87134 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e87134
            | exact resolve b4e87134 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e93881 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 (M.op X2 X0)) X0)) = (M.op y (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e87134 (M.op (M.op X1 (M.op X2 X0)) X0) X0
               have i₂ := b4e290 X0 X1 X2
               grind)
            | exact superpose b4e290 b4e87134
            | exact resolve b4e87134 b4e290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e290 b4e87134
          have b4e127403 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e2301 X1 X1 X0
               have i₂ := b4e55883 X1 X0
               grind)
            | exact superpose b4e55883 b4e2301
            | exact resolve b4e2301 b4e55883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2301
          have b4e127668 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 (M.op X1 X0)) X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e43931 X2 X1 (M.op X1 X0) y
               have i₂ := b4e55883 X0 X1
               grind)
            | exact superpose b4e55883 b4e43931
            | exact resolve b4e43931 b4e55883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55883
          have b4e127685 : ∀ X0 X1 X2 : G, (M.op y (M.op x X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e127668 X0 X1 X2
               have i₂ := b4e93881 X0 X0 X1
               grind)
            | exact superpose b4e93881 b4e127668
            | exact resolve b4e127668 b4e93881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93881 b4e127668
          have b4e127789 : ∀ X0 X1 : G, (M.op (M.op y X1) (M.op (M.op y X0) (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e127403 X0 X1
               have i₂ := b4e37731 X1 (M.op (M.op y X0) (M.op X0 X1))
               grind)
            | exact superpose b4e37731 b4e127403
            | exact resolve b4e127403 b4e37731
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37731 b4e127403
          have b4e128063 : ∀ X1 : G, (M.op (M.op y X1) (M.op y (M.op x X1))) = X1 := by
            intro X1
            first
            | (have i₁ := b4e127789 x X1
               have i₂ := b4e127685 X1 x y
               grind)
            | exact superpose b4e127685 b4e127789
            | exact resolve b4e127789 b4e127685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127789
          have b4e131208 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e9074 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e9074
            | exact resolve b4e9074 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e9074
          have b4e131370 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e131208 X0
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e131208
            | (have j0 := b4e131208 X0
               grind)
            | exact resolve b4e131208 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e131208
          have b4e131393 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b4e131370 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e131370
            | (have j0 := b4e131370 X0
               grind)
            | exact resolve b4e131370 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131370
          have b4e131399 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e131393 X0
               have j1 := b4e16 X0 X0
               grind)
            | (have r₁ := b4e131393 X0
               have r₂ := b4e16 X0 X0
               grind)
            | exact resolve b4e131393 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131393
          have b4e131434 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e75 X0 X0
               have i₂ := b4e131399 (τ X0)
               grind)
            | exact superpose b4e131399 b4e75
            | exact resolve b4e75 b4e131399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e131453 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e131434 X0
               have i₂ := b4e131399 X0
               grind)
            | exact superpose b4e131399 b4e131434
            | exact resolve b4e131434 b4e131399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131399 b4e131434
          have b4e132439 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (τ X0)) X2) = (M.op (τ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e43931 X1 (τ X0) X2 (τ X0)
               have i₂ := b4e131453 X0
               grind)
            | exact superpose b4e131453 b4e43931
            | exact resolve b4e43931 b4e131453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43931
          have b4e136159 : ∀ X0 X1 : G, (M.op y (M.op x (τ X0))) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e127685 (τ X0) (τ X0) X1
               have i₂ := b4e131453 X0
               grind)
            | exact superpose b4e131453 b4e127685
            | exact resolve b4e127685 b4e131453
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e140782 : ∀ X0 X1 : G, (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) X1) = (M.op (τ (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e132439 (M.op (σ x) (σ y)) X0 X1
               have i₂ := b4e34820 (σ x)
               grind)
            | exact superpose b4e34820 b4e132439
            | exact resolve b4e132439 b4e34820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34820
          have b4e141279 : ∀ X0 X1 : G, (M.op (M.op X0 (τ X1)) (τ (M.op X1 X1))) = (τ (M.op (M.op X1 X1) (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e131453 (M.op X1 X1)
               have i₂ := b4e132439 X1 X0 (τ (M.op X1 X1))
               grind)
            | exact superpose b4e132439 b4e131453
            | exact resolve b4e131453 b4e132439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131453 b4e132439
          have b4e141345 : ∀ X0 X1 : G, (M.op (M.op X0 (τ X1)) (τ (M.op X1 X1))) = (τ (M.op y (M.op x X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e141279 X0 X1
               have i₂ := b4e127685 X1 X1 X1
               grind)
            | exact superpose b4e127685 b4e141279
            | exact resolve b4e141279 b4e127685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127685 b4e141279
          have b4e141444 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 (τ (M.op (σ x) (σ y)))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e140782 X0 X1
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e140782
            | exact resolve b4e140782 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e140782
          have b4e141463 : ∀ X1 : G, (M.op y (M.op x (τ X1))) = (τ (M.op y (M.op x X1))) := by
            intro X1
            first
            | (have i₁ := b4e141345 x X1
               have i₂ := b4e136159 X1 x
               grind)
            | exact superpose b4e136159 b4e141345
            | exact resolve b4e141345 b4e136159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136159 b4e141345
          have b4e144630 : (τ (σ y)) = (M.op y (M.op x (τ (M.op (σ x) (σ y))))) := by
            first
            | (have i₁ := b4e141463 (M.op (σ x) (σ y))
               have i₂ := b4e93834
               grind)
            | exact superpose b4e93834 b4e141463
            | exact resolve b4e141463 b4e93834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93834 b4e141463
          have b4e144682 : y = (M.op y (M.op x (τ (M.op (σ x) (σ y))))) := by
            first
            | (have i₁ := b4e144630
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e144630
            | exact resolve b4e144630 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e144630
          have b4e145836 : (τ (M.op (σ x) (σ y))) = (M.op (M.op y (τ (M.op (σ x) (σ y)))) y) := by
            first
            | (have i₁ := b4e128063 (τ (M.op (σ x) (σ y)))
               have i₂ := b4e144682
               grind)
            | exact superpose b4e144682 b4e128063
            | exact resolve b4e128063 b4e144682
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128063 b4e144682
          have b4e145923 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e145836
               have i₂ := b4e141444 y y
               grind)
            | exact superpose b4e141444 b4e145836
            | exact resolve b4e145836 b4e141444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141444 b4e145836
          have b4e146173 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e15 (M.op (σ x) (σ y))
               have i₂ := b4e145923
               grind)
            | exact superpose b4e145923 b4e15
            | exact resolve b4e15 b4e145923
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145923
          have b4e146217 : False := by grind
          exact b4e146217
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e42 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e47 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : y = (k x y) ∨ y = (M.op y x) := by grind
          have b5e61 : y = (k x y) := by
            first
            | (have r₁ := b5e57
               have r₂ := b5e21
               grind)
            | exact resolve b5e57 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e120 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e47 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e120
               have r₂ := b5e23
               grind)
            | exact resolve b5e120 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e122 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e121
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e121
            | exact resolve b5e121 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e121
          have b5e123 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e122
               have i₂ := b5e61
               grind)
            | exact superpose b5e61 b5e122
            | exact resolve b5e122 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e122
          have b5e250 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e42 x x
               grind)
            | exact superpose b5e42 b5e24
            | (have j1 := b5e42 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e42 x y
               grind)
            | exact resolve b5e24 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e295 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e250
          have b5e929 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e295
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e295
            | (have j1 := b5e18 (σ x) (σ x)
               grind)
            | exact resolve b5e295 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e295
          have b5e930 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e929
          have b5e931 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e930
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e930
            | exact resolve b5e930 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e930
          have b5e932 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e931
          have b5e938 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e932
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e932
            | exact resolve b5e932 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e932
          have b5e947 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e938
               grind)
            | exact superpose b5e938 b5e24
            | exact resolve b5e24 b5e938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e952 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e16 (σ x) (σ x)
               have i₂ := b5e938
               grind)
            | exact superpose b5e938 b5e16
            | (have r₁ := b5e16 (σ x) (σ x)
               have r₂ := b5e938
               grind)
            | exact resolve b5e16 b5e938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e938
          have b5e962 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
          clear b5e952
          have b5e964 : (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e962
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e962
            | exact resolve b5e962 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e962
          have b5e1177 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e964
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e964
            | (have j1 := b5e18 x x
               grind)
            | exact resolve b5e964 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e964
          have b5e1199 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x x) := by grind
          clear b5e1177
          have b5e1213 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1199
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1199
            | exact resolve b5e1199 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1199
          have b5e1217 : x = y ∨ x = (M.op x x) := by
            first
            | (have r₁ := b5e1213
               have r₂ := b5e947
               grind)
            | exact resolve b5e1213 b5e947
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e947 b5e1213
          have b5e1221 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e1217
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1217
            | exact resolve b5e1217 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1217
          have b5e1222 : x = y := by grind
          clear b5e1221
          have b5e1323 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1222
               grind)
            | exact superpose b5e1222 b5e23
            | exact resolve b5e23 b5e1222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1330 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e123
               have i₂ := b5e1222
               grind)
            | exact superpose b5e1222 b5e123
            | exact resolve b5e123 b5e1222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123 b5e1222
          have b5e1357 : False := by grind
          exact b5e1357
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X2 X1) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 : G, (M.op (σ x) (M.op X0 (M.op (σ y) X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e35 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e33
        have b6e36 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b6e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e52 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X2 X1) X0)) ∨ (M.op (M.op X2 X1) X0) = (k (M.op X2 X1) X0) ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X2 X1) X1 X2
             have i₂ := b6e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b6e12 X0 X1 X2
             have i₂ := b6e17 X0 (M.op (M.op X2 X1) X0)
             grind)
          | exact superpose b6e17 b6e12
          | (have j1 := b6e17 (M.op X2 X1) X0
             grind)
          | exact resolve b6e12 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 ∨ (k X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e72 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          first
          | (have i₁ := b6e26 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e26
          | exact resolve b6e26 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e372 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e47 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e373 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e372 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e372
        have b6e518 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X1 X0
             have i₂ := b6e52 X1 X1 X0
             grind)
          | exact superpose b6e52 b6e12
          | (have j1 := b6e52 X1 X1 X0
             grind)
          | exact resolve b6e12 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e539 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (k (M.op X0 X1) X1) ∨ (M.op X1 (M.op X0 X1)) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e518 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e518
        have b6e1168 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e539 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e539
          | exact resolve b6e539 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e539
        have b6e1189 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e1168
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e1168
          | exact resolve b6e1168 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1168
        have b6e1192 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e1189
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1189
          | exact resolve b6e1189 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1189
        have b6e1967 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e1192
             grind)
          | exact superpose b6e1192 b6e72
          | exact resolve b6e72 b6e1192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1968 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e1192
             grind)
          | exact superpose b6e1192 b6e19
          | exact resolve b6e19 b6e1192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1192
        have b6e2000 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e1967
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e1967
          | exact resolve b6e1967 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36 b6e1967
        have b6e2051 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e2000
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e2000
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e2000 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2000
        have b6e2102 : (σ y) = (σ (k y x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e2051
             have r₂ := b6e1968
             grind)
          | exact resolve b6e2051 b6e1968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1968 b6e2051
        have b6e2106 : (σ y) = (σ (k y x)) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e2102
             have r₂ := b6e21
             grind)
          | exact resolve b6e2102 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2102
        have b6e2110 : (σ y) = (σ (k y x)) := by
          first
          | (have r₁ := b6e2106
             have r₂ := b6e20
             grind)
          | exact resolve b6e2106 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2106
        have b6e2201 : (k y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e2110
             grind)
          | exact superpose b6e2110 b6e13
          | exact resolve b6e13 b6e2110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2110
        have b6e2239 : y = (k y x) := by
          first
          | (have i₁ := b6e2201
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2201
          | exact resolve b6e2201 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2201
        have b6e2420 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
          first
          | (have i₁ := b6e61 x y
             have i₂ := b6e2239
             grind)
          | exact superpose b6e2239 b6e61
          | (have j0 := b6e61 y x
             grind)
          | exact resolve b6e61 b6e2239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61
        have b6e2421 : y = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e2239
             grind)
          | exact superpose b6e2239 b6e17
          | (have j0 := b6e17 y x
             grind)
          | exact resolve b6e17 b6e2239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2422 : x = (M.op x y) ∨ x = (M.op y y) := by
          first
          | (have r₁ := b6e2421
             have r₂ := b6e20
             grind)
          | exact resolve b6e2421 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2421
        have b6e2423 : x = (M.op x y) ∨ x = y := by
          first
          | (have r₁ := b6e2420
             have r₂ := b6e20
             grind)
          | exact resolve b6e2420 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2420
        have b6e2474 : x ≠ x ∨ (k y x) = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e2423
             grind)
          | exact superpose b6e2423 b6e15
          | (have j0 := b6e15 y x
             grind)
          | (have r₁ := b6e15 y x
             have r₂ := b6e2423
             grind)
          | exact resolve b6e15 b6e2423
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2423
        have b6e2491 : (k y x) = (M.op y y) ∨ x = y := by grind
        clear b6e2474
        have b6e2496 : y = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b6e2491
             have i₂ := b6e2239
             grind)
          | exact superpose b6e2239 b6e2491
          | exact resolve b6e2491 b6e2239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2491
        have b6e3209 : x ≠ x ∨ (k y x) = (M.op y y) ∨ x = (M.op y y) := by
          first
          | (have i₁ := b6e15 y x
             have i₂ := b6e2422
             grind)
          | exact superpose b6e2422 b6e15
          | (have j0 := b6e15 y x
             grind)
          | (have r₁ := b6e15 y x
             have r₂ := b6e2422
             grind)
          | exact resolve b6e15 b6e2422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2422
        have b6e3231 : (k y x) = (M.op y y) ∨ x = (M.op y y) := by grind
        clear b6e3209
        have b6e3238 : x = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e3231
             have i₂ := b6e2239
             grind)
          | exact superpose b6e2239 b6e3231
          | exact resolve b6e3231 b6e2239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2239 b6e3231
        have b6e4234 : x ≠ y ∨ y = (M.op y y) := by grind
        clear b6e3238
        have b6e4236 : y = (M.op y y) := by
          first
          | (have r₁ := b6e4234
             have r₂ := b6e2496
             grind)
          | exact resolve b6e4234 b6e2496
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2496 b6e4234
        have b6e4352 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b6e15 y y
             have i₂ := b6e4236
             grind)
          | exact superpose b6e4236 b6e15
          | (have r₁ := b6e15 y y
             have r₂ := b6e4236
             grind)
          | exact resolve b6e15 b6e4236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4373 : y = (k y y) := by grind
        clear b6e4352
        have b6e4516 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e373 y
             have i₂ := b6e4373
             grind)
          | exact superpose b6e4373 b6e373
          | (have j0 := b6e373 y
             grind)
          | exact resolve b6e373 b6e4373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e373 b6e4373
        have b6e4523 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e4516
        have b6e4795 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b6e26 (σ y)
             have i₂ := b6e4523
             grind)
          | exact superpose b6e4523 b6e26
          | exact resolve b6e26 b6e4523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e4835 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e4795
             have i₂ := b6e4523
             grind)
          | exact superpose b6e4523 b6e4795
          | exact resolve b6e4795 b6e4523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4523 b6e4795
        have b6e4859 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e4835
             grind)
          | exact superpose b6e4835 b6e72
          | exact resolve b6e72 b6e4835
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e4919 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4859
             have i₂ := b6e4835
             grind)
          | exact superpose b6e4835 b6e4859
          | exact resolve b6e4859 b6e4835
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4835 b6e4859
        have b6e5179 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e4919
             grind)
          | exact superpose b6e4919 b6e13
          | exact resolve b6e13 b6e4919
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4919
        have b6e5239 : x = y := by
          first
          | (have i₁ := b6e5179
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e5179
          | exact resolve b6e5179 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5179
        have b6e5655 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e5239
             grind)
          | exact superpose b6e5239 b6e21
          | exact resolve b6e21 b6e5239
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5239
        have b6e5707 : False := by grind
        exact b6e5707
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e45 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e362 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e57 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e57
            | exact resolve b7e57 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e420 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
          clear b7e362
          have b7e434 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e420
               have r₂ := b7e45
               grind)
            | exact resolve b7e420 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45 b7e420
          have b7e460 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e434
               grind)
            | exact superpose b7e434 b7e14
            | exact resolve b7e14 b7e434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e434
          have b7e475 : y = (k x x) := by
            first
            | (have i₁ := b7e460
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e460
            | exact resolve b7e460 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e460
          have b7e519 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e475
               grind)
            | exact superpose b7e475 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e520 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e519
          have b7e522 : x = (M.op x x) := by
            first
            | (have r₁ := b7e520
               have r₂ := b7e22
               grind)
            | exact resolve b7e520 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e520
          have b7e531 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e522
               grind)
            | exact superpose b7e522 b7e22
            | exact resolve b7e22 b7e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e534 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b7e16 x x
               have i₂ := b7e522
               grind)
            | exact superpose b7e522 b7e16
            | (have r₁ := b7e16 x x
               have r₂ := b7e522
               grind)
            | exact resolve b7e16 b7e522
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e522
          have b7e541 : x = (k x x) := by grind
          clear b7e534
          have b7e661 : x = y := by
            first
            | (have i₁ := b7e475
               have i₂ := b7e541
               grind)
            | exact superpose b7e541 b7e475
            | exact resolve b7e475 b7e541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e475 b7e541
          have b7e673 : False := by grind
          exact b7e673
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e60 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e162 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e163 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e162
               have r₂ := b8e23
               grind)
            | exact resolve b8e162 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162
          have b8e164 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e163
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e163
            | exact resolve b8e163 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e163
          have b8e165 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e164
               grind)
            | exact superpose b8e164 b8e20
            | exact resolve b8e20 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164
          have b8e175 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e165
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e165
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e165 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165
          have b8e176 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e175
          have b8e178 : y = (M.op y x) := by
            first
            | (have r₁ := b8e176
               have r₂ := b8e22
               grind)
            | exact resolve b8e176 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176
          have b8e180 : False := by grind
          exact b8e180

/-- `Equation840`: `x = x ◇ ((y ◇ x) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation840 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law840 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law840.models_iff G M).mp hM
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
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b2e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : x = (M.op x y) := by
            first
            | (have i₁ := b2e43 x x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e43
            | exact resolve b2e43 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e45 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e43 (σ x) (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e43
            | exact resolve b2e43 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43
          have b2e112 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e45
               grind)
            | exact superpose b2e45 b2e20
            | exact resolve b2e20 b2e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e118 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b2e112
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e112
            | exact resolve b2e112 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44 b2e112
          have b2e119 : False := by grind
          exact b2e119
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
          have b3e27 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e27
            | exact resolve b3e27 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e27
          have b3e29 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e28
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e28
            | exact resolve b3e28 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e28
          have b3e30 : False := by grind
          exact b3e30
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b4e25 : x ≠ (M.op x x) := by grind
            have b4e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e28 : False := by grind
            exact b4e28
          · have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
            have b5e26 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e29 : x ≠ y := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e26
              | exact resolve b5e26 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e30 : x = (k x y) := by grind
            have b5e45 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b5e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b5e45
            have b5e51 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b5e50
                 have r₂ := b5e23
                 grind)
              | exact resolve b5e50 b5e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e50
            have b5e52 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b5e51
                 have i₂ := b5e20 x y
                 grind)
              | exact superpose b5e20 b5e51
              | exact resolve b5e51 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e51
            have b5e53 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e52
                 have i₂ := b5e30
                 grind)
              | exact superpose b5e30 b5e52
              | exact resolve b5e52 b5e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e52
            have b5e57 : y = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 y
                 have i₂ := b5e53
                 grind)
              | exact superpose b5e53 b5e15
              | exact resolve b5e15 b5e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e53
            have b5e58 : x = y := by
              first
              | (have i₁ := b5e57
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e57
              | exact resolve b5e57 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e57
            have b5e61 : False := by grind
            exact b5e61
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op x x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b6e27 : x = (k x x) := by grind
          have b6e28 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e26
               grind)
            | exact superpose b6e26 b6e23
            | exact resolve b6e23 b6e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b6e270 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e58 x x
               grind)
            | exact superpose b6e58 b6e22
            | (have j1 := b6e58 x x
               grind)
            | (have r₁ := b6e22
               have r₂ := b6e58 x y
               grind)
            | exact resolve b6e22 b6e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e58
          have b6e325 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e270
          have b6e332 : (σ y) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b6e325
               have r₂ := b6e28
               grind)
            | exact resolve b6e325 b6e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e325
          have b6e338 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b6e332
               have i₂ := b6e27
               grind)
            | exact superpose b6e27 b6e332
            | exact resolve b6e332 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e332
          have b6e340 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e338
               have i₂ := b6e26
               grind)
            | exact superpose b6e26 b6e338
            | exact resolve b6e338 b6e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26 b6e338
          have b6e341 : False := by grind
          exact b6e341
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b7e25 : x ≠ (M.op x x) := by grind
            have b7e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : False := by grind
            exact b7e28
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b8e22 : y = (M.op x x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e29 : x = (k x y) := by grind
            have b8e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                 have i₂ := b8e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e36 : x = (M.op x y) := by
              first
              | (have i₁ := b8e35 x x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e35
              | exact resolve b8e35 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
            have b8e317 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e21
                 have i₂ := b8e54 x y
                 grind)
              | exact superpose b8e54 b8e21
              | (have j1 := b8e54 x y
                 grind)
              | exact resolve b8e21 b8e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e54
            have b8e378 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b8e317
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e317 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e317
            have b8e383 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have r₁ := b8e378
                 have r₂ := b8e24
                 grind)
              | exact resolve b8e378 b8e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e378
            have b8e384 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b8e383
                 have i₂ := b8e29
                 grind)
              | exact superpose b8e29 b8e383
              | exact resolve b8e383 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e383
            have b8e385 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b8e384
                 have i₂ := b8e36
                 grind)
              | exact superpose b8e36 b8e384
              | exact resolve b8e384 b8e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36 b8e384
            have b8e386 : False := by grind
            exact b8e386
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e22 : x = (M.op x y) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e20
            | exact resolve b9e20 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e51 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b9e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e54 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e51 (σ x) (σ x)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e51
            | exact resolve b9e51 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e59 : False := by grind
          exact b9e59
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b10e25 : x ≠ (M.op x x) := by grind
            have b10e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : False := by grind
            exact b10e28
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e23 : x = (M.op x y) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e21
              | exact resolve b11e21 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                 have i₂ := b11e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e45 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b11e43 (σ x) (σ x)
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e43
              | exact resolve b11e43 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e43
            have b11e50 : False := by grind
            exact b11e50
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op x y) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e29 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e30 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e29
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e29
              | exact resolve b12e29 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e29
            have b12e31 : False := by grind
            exact b12e31
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b13e27 : x ≠ (M.op x x) := by grind
              have b13e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : False := by grind
              exact b13e30
            · have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op x y) := by grind
              have b14e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e30 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e22
                | exact resolve b14e22 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e31 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b14e30
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e30
                | exact resolve b14e30 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e30
              have b14e32 : False := by grind
              exact b14e32
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : x = (M.op x y) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
            have b15e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 (τ X0) X1
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e20
              | exact resolve b15e20 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e34 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
              intro X0
              grind
            clear b15e31
            have b15e38 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e34 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e34
              | exact resolve b15e34 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                 have i₂ := b15e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e50 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
            have b15e55 : y = (M.op x x) ∨ y = (k x y) := by grind
            clear b15e50
            have b15e56 : x = y ∨ y = (k x y) := by
              first
              | (have i₁ := b15e55
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e55
              | exact resolve b15e55 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e55
            have b15e57 : y = (k x y) := by
              first
              | (have r₁ := b15e56
                 have r₂ := b15e28
                 grind)
              | exact resolve b15e56 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e56
            have b15e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e20 X0 X1
                 have i₂ := b15e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b15e19 b15e20
              | (have j1 := b15e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b15e20 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e69 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e43 X1 X1
                 have i₂ := b15e19 X1 X0
                 grind)
              | (have i₁ := b15e43 X0 X1
                 have i₂ := b15e19 X0 (M.op X0 X1)
                 grind)
              | exact superpose b15e19 b15e43
              | (have j1 := b15e19 X1 X0
                 grind)
              | exact resolve b15e43 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have j0 := b15e69 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e69
            have b15e325 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b15e43 (σ X0) (σ X1)
                 have i₂ := b15e62 X0 X1
                 grind)
              | exact superpose b15e62 b15e43
              | (have j1 := b15e62 X0 X1
                 grind)
              | exact resolve b15e43 b15e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e351 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b15e43 (σ X1) (σ X1)
                 have i₂ := b15e62 X1 X0
                 grind)
              | exact superpose b15e62 b15e43
              | (have j1 := b15e62 X1 X0
                 grind)
              | exact resolve b15e43 b15e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e43 b15e62
            have b15e356 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b15e351 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e351
            have b15e573 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b15e38 X0
                 have i₂ := b15e73 (σ (M.op (τ X0) (τ X0))) X0
                 grind)
              | exact superpose b15e73 b15e38
              | (have j1 := b15e73 (σ (M.op (τ X0) (τ X0))) X0
                 grind)
              | exact resolve b15e38 b15e73
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38 b15e73
            have b15e585 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
              intro X0
              first
              | (have j0 := b15e573 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e573
            have b15e591 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b15e585 (σ X0)
                 have i₂ := b15e15 X0
                 grind)
              | exact superpose b15e15 b15e585
              | exact resolve b15e585 b15e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e585
            have b15e732 : (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e591 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e591
              | exact resolve b15e591 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e591
            have b15e4268 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e325 x y
                 have i₂ := b15e57
                 grind)
              | exact superpose b15e57 b15e325
              | (have j0 := b15e325 y y
                 grind)
              | exact resolve b15e325 b15e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e325
            have b15e4443 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b15e4268
                 have r₂ := b15e24
                 grind)
              | exact resolve b15e4268 b15e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4268
            have b15e4448 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have r₁ := b15e4443
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e4443 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4443
            have b15e4462 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) (σ y))) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X0 X1 (σ y)
                 have i₂ := b15e4448
                 grind)
              | exact superpose b15e4448 b15e14
              | exact resolve b15e14 b15e4448
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e4448
            have b15e11684 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
              first
              | (have i₁ := b15e4462 (σ x) (σ x)
                 have i₂ := b15e732
                 grind)
              | exact superpose b15e732 b15e4462
              | exact resolve b15e4462 b15e732
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e732 b15e4462
            have b15e16413 : (σ x) = (M.op (σ x) (σ (k x y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e11684
                 have i₂ := b15e356 y x
                 grind)
              | exact superpose b15e356 b15e11684
              | (have j1 := b15e356 (k x y) x
                 grind)
              | exact resolve b15e11684 b15e356
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e356 b15e11684
            have b15e16474 : (σ x) = (M.op (σ x) (σ (k x y))) := by
              first
              | (have r₁ := b15e16413
                 have r₂ := b15e25
                 grind)
              | exact resolve b15e16413 b15e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e16413
            have b15e16478 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b15e16474
                 have i₂ := b15e57
                 grind)
              | exact superpose b15e57 b15e16474
              | exact resolve b15e16474 b15e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e57 b15e16474
            have b15e16480 : False := by grind
            exact b15e16480
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b16e27 : x ≠ (M.op x x) := by grind
              have b16e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e30 : False := by grind
              exact b16e30
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op x x) := by grind
              have b17e24 : x = (M.op x y) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              have b17e28 : x ≠ (M.op x x) := by grind
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
              have b17e33 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b17e15 y x X0
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e15 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                   have i₂ := b17e15 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e36 : y = (M.op y x) := by
                first
                | (have i₁ := b17e35 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e35
                | exact resolve b17e35 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b17e35 X0 (M.op X1 X0)
                   have i₂ := b17e35 X1 X0
                   grind)
                | exact superpose b17e35 b17e35
                | exact resolve b17e35 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
              have b17e46 : y = (M.op x x) ∨ y = (k x y) := by grind
              clear b17e41
              have b17e47 : y = (k x y) := by
                first
                | (have r₁ := b17e46
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e46 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e46
              have b17e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e21 X0 X1
                   have i₂ := b17e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b17e20 b17e21
                | (have j1 := b17e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b17e21 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e56 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e35 X1 X1
                   have i₂ := b17e20 X1 X0
                   grind)
                | (have i₁ := b17e35 X0 X1
                   have i₂ := b17e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b17e20 b17e35
                | (have j1 := b17e20 X1 X0
                   grind)
                | exact resolve b17e35 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e60 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b17e56 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e56
              have b17e68 : ∀ X0 : G, y ≠ y ∨ (M.op x (M.op X0 X0)) = (M.op y y) ∨ (M.op x (M.op X0 X0)) = (k y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b17e19 y (M.op x (M.op X0 X0))
                   have i₂ := b17e33 X0
                   grind)
                | exact superpose b17e33 b17e19
                | (have j0 := b17e19 y (M.op x (M.op X0 X0))
                   grind)
                | (have r₁ := b17e19 y (M.op x (M.op X0 X0))
                   have r₂ := b17e33 X0
                   grind)
                | exact resolve b17e19 b17e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e33
              have b17e71 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (k y (M.op x (M.op X0 X0))) ∨ (M.op x (M.op X0 X0)) = (M.op y y) := by
                intro X0
                first
                | (have j0 := b17e68 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e68
              have b17e80 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b17e19 (M.op X0 X1) X1
                   have i₂ := b17e38 X1 X0
                   grind)
                | exact superpose b17e38 b17e19
                | (have j0 := b17e19 (M.op X0 X1) X1
                   grind)
                | (have r₁ := b17e19 (M.op X1 X0) X0
                   have r₂ := b17e38 X0 X1
                   grind)
                | exact resolve b17e19 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e83 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = X1 ∨ (k (M.op X0 X1) X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b17e80 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e80
              have b17e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
              have b17e166 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                grind
              clear b17e105
              have b17e179 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e166 X0
                   have i₂ := b17e16 X0
                   grind)
                | exact superpose b17e16 b17e166
                | exact resolve b17e166 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e166
              have b17e279 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e35 (σ X0) (σ X1)
                   have i₂ := b17e51 X0 X1
                   grind)
                | exact superpose b17e51 b17e35
                | (have j1 := b17e51 X0 X1
                   grind)
                | exact resolve b17e35 b17e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e303 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e35 (σ X1) (σ X1)
                   have i₂ := b17e51 X1 X0
                   grind)
                | exact superpose b17e51 b17e35
                | (have j1 := b17e51 X1 X0
                   grind)
                | exact resolve b17e35 b17e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e51
              have b17e308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
                intro X0 X1
                first
                | (have j0 := b17e303 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e303
              have b17e400 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 ∨ (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b17e179 X0
                   have i₂ := b17e60 (τ (M.op (σ X0) (σ X0))) X0
                   grind)
                | exact superpose b17e60 b17e179
                | (have j1 := b17e60 (τ (M.op (σ X0) (σ X0))) X0
                   grind)
                | exact resolve b17e179 b17e60
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e60 b17e179
              have b17e407 : ∀ X0 : G, (M.op X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have j0 := b17e400 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e400
              have b17e496 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b17e407 (τ X0)
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e407
                | exact resolve b17e407 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e407
              have b17e604 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
                intro X0
                first
                | (have i₁ := b17e35 (τ X0) (τ (M.op X0 X0))
                   have i₂ := b17e496 X0
                   grind)
                | exact superpose b17e496 b17e35
                | exact resolve b17e35 b17e496
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e496
              have b17e1181 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b17e38 (σ X0) (σ X1)
                   have i₂ := b17e308 X0 X1
                   grind)
                | exact superpose b17e308 b17e38
                | (have j1 := b17e308 X1 (k X0 X1)
                   grind)
                | exact resolve b17e38 b17e308
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e38 b17e308
              have b17e2204 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e279 x y
                   have i₂ := b17e47
                   grind)
                | exact superpose b17e47 b17e279
                | (have j0 := b17e279 y y
                   grind)
                | exact resolve b17e279 b17e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e47 b17e279
              have b17e2366 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b17e2204
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e2204 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2204
              have b17e2372 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have r₁ := b17e2366
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e2366 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2366
              have b17e2419 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) := by
                first
                | (have i₁ := b17e604 (σ y)
                   have i₂ := b17e2372
                   grind)
                | exact superpose b17e2372 b17e604
                | exact resolve b17e604 b17e2372
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2372
              have b17e2435 : y = (M.op y y) := by
                first
                | (have i₁ := b17e2419
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e2419
                | exact resolve b17e2419 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2419
              have b17e2828 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b17e71 y
                   have i₂ := b17e2435
                   grind)
                | exact superpose b17e2435 b17e71
                | exact resolve b17e71 b17e2435
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e71 b17e2435
              have b17e2868 : x = (k y x) ∨ y = (M.op x y) := by
                first
                | (have i₁ := b17e2828
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e2828
                | exact resolve b17e2828 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2828
              have b17e2871 : x = (k y x) ∨ x = y := by
                first
                | (have i₁ := b17e2868
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e2868
                | exact resolve b17e2868 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2868
              have b17e10004 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) ∨ (k (M.op X1 X0) X0) = X0 := by
                intro X0 X1
                grind
              clear b17e83
              have b17e1455560 : y = (k y x) ∨ x = (k y x) := by
                first
                | (have i₁ := b17e10004 x y
                   have i₂ := b17e36
                   grind)
                | exact superpose b17e36 b17e10004
                | exact resolve b17e10004 b17e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e36 b17e10004
              have b17e1455575 : x ≠ y ∨ x = (k y x) := by grind
              clear b17e1455560
              have b17e1455581 : x = (k y x) := by
                first
                | (have r₁ := b17e1455575
                   have r₂ := b17e2871
                   grind)
                | exact resolve b17e1455575 b17e2871
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e2871 b17e1455575
              have b17e1455588 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b17e1181 y x
                   have i₂ := b17e1455581
                   grind)
                | exact superpose b17e1455581 b17e1181
                | (have j0 := b17e1181 y x
                   grind)
                | exact resolve b17e1181 b17e1455581
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1181 b17e1455581
              have b17e1651766 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b17e35 (σ y) (σ x)
                   have i₂ := b17e1455588
                   grind)
                | exact superpose b17e1455588 b17e35
                | exact resolve b17e35 b17e1455588
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35 b17e1455588
              have b17e1651768 : (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have r₁ := b17e1651766
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e1651766 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1651766
              have b17e1651827 : (τ (σ x)) = (M.op (τ (σ x)) (τ (σ x))) := by
                first
                | (have i₁ := b17e604 (σ x)
                   have i₂ := b17e1651768
                   grind)
                | exact superpose b17e1651768 b17e604
                | exact resolve b17e604 b17e1651768
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e604 b17e1651768
              have b17e1652234 : x = (M.op x x) := by
                first
                | (have i₁ := b17e1651827
                   have i₂ := b17e16 x
                   grind)
                | exact superpose b17e16 b17e1651827
                | exact resolve b17e1651827 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e1651827
              have b17e1652274 : False := by grind
              exact b17e1652274
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op x x) := by grind
          have b18e22 : x ≠ (M.op x y) := by grind
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
          have b18e28 : (σ x) = (k (σ x) (σ y)) := by grind
          have b18e29 : (σ x) = (σ (k x y)) := by
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
          have b18e30 : (k x y) = (τ (σ x)) := by
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
          have b18e31 : x = (k x y) := by
            first
            | (have i₁ := b18e30
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e30
            | exact resolve b18e30 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e74 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b18e31
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e31
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e31 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e31
          have b18e84 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b18e74
          have b18e89 : y = (M.op x x) := by
            first
            | (have r₁ := b18e84
               have r₂ := b18e22
               grind)
            | exact resolve b18e84 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e84
          have b18e92 : x = y := by
            first
            | (have i₁ := b18e89
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e89
            | exact resolve b18e89 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e89
          have b18e95 : False := by grind
          exact b18e95
        · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
          · have b19e25 : x ≠ (M.op x x) := by grind
            have b19e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : False := by grind
            exact b19e28
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op x x) := by grind
            have b20e23 : x ≠ (M.op x y) := by grind
            have b20e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ x) = (k (σ x) (σ y)) := by grind
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
            have b20e34 : (k x y) = (τ (σ x)) := by
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
            have b20e35 : x = (k x y) := by
              first
              | (have i₁ := b20e34
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e34
              | exact resolve b20e34 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e34
            have b20e62 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
            have b20e72 : x = (M.op x y) ∨ y = (M.op x x) := by grind
            clear b20e62
            have b20e75 : y = (M.op x x) := by
              first
              | (have r₁ := b20e72
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e72 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e72
            have b20e78 : False := by grind
            exact b20e78
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op x x) := by grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
            have b21e33 : ∀ X0 : G, x = (M.op x (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b21e14 x x X0
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e14
              | exact resolve b21e14 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e37 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b21e14 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                 have i₂ := b21e14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b21e49 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
            clear b21e44
            have b21e50 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e49
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e49 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e51 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e50
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e50
              | exact resolve b21e50 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e54 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e51
                 grind)
              | exact superpose b21e51 b21e15
              | exact resolve b21e15 b21e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e51
            have b21e55 : y = (k x y) := by
              first
              | (have i₁ := b21e54
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e54
              | exact resolve b21e54 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e78 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e55
                 grind)
              | exact superpose b21e55 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e55
            have b21e79 : y = (M.op x y) ∨ y = (M.op x x) := by
              first
              | (have r₁ := b21e78
                 have r₂ := b21e23
                 grind)
              | exact resolve b21e78 b21e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e78
            have b21e81 : x = y ∨ y = (M.op x y) := by
              first
              | (have i₁ := b21e79
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e79
              | exact resolve b21e79 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e79
            have b21e83 : y = (M.op x y) := by
              first
              | (have r₁ := b21e81
                 have r₂ := b21e28
                 grind)
              | exact resolve b21e81 b21e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e28 b21e81
            have b21e97 : y = (M.op y y) := by
              first
              | (have i₁ := b21e37 x y
                 have i₂ := b21e83
                 grind)
              | exact superpose b21e83 b21e37
              | exact resolve b21e37 b21e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e37
            have b21e119 : x = (M.op x (M.op x y)) := by
              first
              | (have i₁ := b21e33 y
                 have i₂ := b21e97
                 grind)
              | exact superpose b21e97 b21e33
              | exact resolve b21e33 b21e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e33 b21e97
            have b21e125 : x = (M.op x y) := by
              first
              | (have i₁ := b21e119
                 have i₂ := b21e83
                 grind)
              | exact superpose b21e83 b21e119
              | exact resolve b21e119 b21e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e83 b21e119
            have b21e126 : False := by grind
            exact b21e126
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b22e27 : x ≠ (M.op x x) := by grind
              have b22e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : False := by grind
              exact b22e30
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b23e23 : y ≠ (M.op x x) := by grind
              have b23e24 : x ≠ (M.op x y) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              have b23e28 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b23e22
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e22
                | exact resolve b23e22 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b23e21 (τ X0) X1
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e21
                | exact resolve b23e21 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e34 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                grind
              clear b23e31
              have b23e38 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b23e34 X0
                   have i₂ := b23e17 X0
                   grind)
                | exact superpose b23e17 b23e34
                | exact resolve b23e34 b23e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e39 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ x) (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b23e15 (σ y) (σ x) X0
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e41 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X1 X0 (M.op (M.op X0 X1) (M.op X0 X1))
                   have i₂ := b23e15 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e44 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
                intro X0 X1
                first
                | (have i₁ := b23e41 X0 (M.op X1 X0)
                   have i₂ := b23e41 X1 X0
                   grind)
                | exact superpose b23e41 b23e41
                | exact resolve b23e41 b23e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e47 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
              have b23e52 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
              clear b23e47
              have b23e53 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e52
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e52 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52
              have b23e54 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e53
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e53
                | exact resolve b23e53 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e53
              have b23e57 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e54
                   grind)
                | exact superpose b23e54 b23e16
                | exact resolve b23e16 b23e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e54
              have b23e58 : y = (k x y) := by
                first
                | (have i₁ := b23e57
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e57
                | exact resolve b23e57 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e57
              have b23e69 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b23e41 X1 X1
                   have i₂ := b23e20 X1 X0
                   grind)
                | (have i₁ := b23e41 X0 X1
                   have i₂ := b23e20 X0 (M.op X0 X1)
                   grind)
                | exact superpose b23e20 b23e41
                | (have j1 := b23e20 X1 X0
                   grind)
                | exact resolve b23e41 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b23e69 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e69
              have b23e77 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e58
                   grind)
                | exact superpose b23e58 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e58
              have b23e78 : y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b23e77
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e77 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e77
              have b23e80 : y = (M.op x y) := by
                first
                | (have r₁ := b23e78
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e78 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e78
              have b23e91 : (σ x) ≠ (σ y) := by
                first
                | (have i₁ := b23e30
                   have i₂ := b23e80
                   grind)
                | exact superpose b23e80 b23e30
                | exact resolve b23e30 b23e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e94 : y = (M.op y y) := by
                first
                | (have i₁ := b23e41 x y
                   have i₂ := b23e80
                   grind)
                | exact superpose b23e80 b23e41
                | exact resolve b23e41 b23e80
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e80
              have b23e99 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (M.op X0 X0)) = (k (σ y) (M.op (σ x) (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b23e19 (σ y) (M.op (σ x) (M.op X0 X0))
                   have i₂ := b23e39 X0
                   grind)
                | exact superpose b23e39 b23e19
                | (have j0 := b23e19 (σ y) (M.op (σ x) (M.op X0 X0))
                   grind)
                | (have r₁ := b23e19 (σ y) (M.op (σ x) (M.op X0 X0))
                   have r₂ := b23e39 X0
                   grind)
                | exact resolve b23e19 b23e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39
              have b23e102 : ∀ X0 : G, (M.op (σ x) (M.op X0 X0)) = (k (σ y) (M.op (σ x) (M.op X0 X0))) ∨ (M.op (σ x) (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
                intro X0
                first
                | (have j0 := b23e99 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e99
              have b23e462 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b23e38 X0
                   have i₂ := b23e73 (σ (M.op (τ X0) (τ X0))) X0
                   grind)
                | exact superpose b23e73 b23e38
                | (have j1 := b23e73 (σ (M.op (τ X0) (τ X0))) X0
                   grind)
                | exact resolve b23e38 b23e73
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e472 : ∀ X0 : G, (M.op X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have j0 := b23e462 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e462
              have b23e569 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b23e472 (σ X0)
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e472
                | exact resolve b23e472 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e472
              have b23e691 : (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e569 y
                   have i₂ := b23e94
                   grind)
                | exact superpose b23e94 b23e569
                | exact resolve b23e569 b23e94
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e94 b23e569
              have b23e2528 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b23e102 (σ y)
                   have i₂ := b23e691
                   grind)
                | exact superpose b23e691 b23e102
                | exact resolve b23e102 b23e691
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e102 b23e691
              have b23e2556 : (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b23e2528
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e2528
                | exact resolve b23e2528 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2528
              have b23e2561 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b23e2556
                   have i₂ := b23e21 y x
                   grind)
                | exact superpose b23e21 b23e2556
                | exact resolve b23e2556 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2556
              have b23e2562 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b23e2561
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e2561
                | exact resolve b23e2561 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2561
              have b23e2563 : (σ x) = (σ (k y x)) := by
                first
                | (have r₁ := b23e2562
                   have r₂ := b23e91
                   grind)
                | exact resolve b23e2562 b23e91
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e91 b23e2562
              have b23e2568 : (k y x) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k y x)
                   have i₂ := b23e2563
                   grind)
                | exact superpose b23e2563 b23e16
                | exact resolve b23e16 b23e2563
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2563
              have b23e2603 : x = (k y x) := by
                first
                | (have i₁ := b23e2568
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e2568
                | exact resolve b23e2568 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e2568
              have b23e2929 : y = (M.op y x) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e73 x y
                   have i₂ := b23e2603
                   grind)
                | exact superpose b23e2603 b23e73
                | (have j0 := b23e73 x y
                   grind)
                | exact resolve b23e73 b23e2603
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e73 b23e2603
              have b23e3001 : x = (M.op x y) ∨ x = (M.op y x) := by
                first
                | (have i₁ := b23e41 y x
                   have i₂ := b23e2929
                   grind)
                | exact superpose b23e2929 b23e41
                | exact resolve b23e41 b23e2929
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e41 b23e2929
              have b23e3019 : x = (M.op y x) := by
                first
                | (have r₁ := b23e3001
                   have r₂ := b23e24
                   grind)
                | exact resolve b23e3001 b23e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e3001
              have b23e3254 : x = (M.op x x) := by
                first
                | (have i₁ := b23e44 x y
                   have i₂ := b23e3019
                   grind)
                | exact superpose b23e3019 b23e44
                | exact resolve b23e44 b23e3019
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e44 b23e3019
              have b23e3269 : False := by grind
              exact b23e3269
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op x x) := by grind
            have b24e23 : x ≠ (M.op x y) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b24e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
            have b24e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X0 X1
                 have i₂ := b24e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e291 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e57 x y
                 grind)
              | exact superpose b24e57 b24e21
              | (have j1 := b24e57 x y
                 grind)
              | exact resolve b24e21 b24e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e57
            have b24e354 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b24e291
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e291 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e291
            have b24e360 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have r₁ := b24e354
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e354 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e354
            have b24e361 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b24e360
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e360
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e360 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e360
            have b24e362 : y = (M.op x x) ∨ x = (M.op x y) := by grind
            clear b24e361
            have b24e363 : y = (M.op x x) := by
              first
              | (have r₁ := b24e362
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e362 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e362
            have b24e364 : x = y := by
              first
              | (have i₁ := b24e363
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e363
              | exact resolve b24e363 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e363
            have b24e365 : False := by grind
            exact b24e365
          · rcases eq_or_ne (M.op x x) (x) with h2b | h2b
            · have b25e27 : x ≠ (M.op x x) := by grind
              have b25e28 : x = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e30 : False := by grind
              exact b25e30
            · have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : y ≠ (M.op x x) := by grind
              have b26e24 : x ≠ (M.op x y) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X0 X1
                   have i₂ := b26e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e224 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e58 x y
                   grind)
                | exact superpose b26e58 b26e22
                | (have j1 := b26e58 x y
                   grind)
                | exact resolve b26e22 b26e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58
              have b26e277 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e224
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e224 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e224
              have b26e282 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b26e277
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e277 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e277
              have b26e283 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e282
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e282
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e282 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e282
              have b26e284 : y = (M.op x x) ∨ x = (M.op x y) := by grind
              clear b26e283
              have b26e285 : x = (M.op x y) := by
                first
                | (have r₁ := b26e284
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e284 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e284
              have b26e286 : False := by grind
              exact b26e286

/-- `Equation887`: `x = y ◇ ((x ◇ y) ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation887 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law887.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e11 y x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ y) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
           have i₂ := b0e11 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : y = (M.op x y) := by
        first
        | (have i₁ := b0e35 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 (M.op X0 X1) X2
           have i₂ := b0e35 X0 X1
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e75 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 x (M.op y (M.op X0 X0)) X1
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e78 : ∀ X0 : G, x = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e75 X0 x
           have i₂ := b0e43 y (M.op X0 X0) x
           grind)
        | exact superpose b0e43 b0e75
        | exact resolve b0e75 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75
      have b0e88 : ∀ X0 : G, (M.op X0 x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 X0 X0
           have i₂ := b0e78 (M.op X0 X0)
           grind)
        | exact superpose b0e78 b0e11
        | exact resolve b0e11 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e101 : ∀ X0 : G, (M.op x X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x
           have i₂ := b0e88 X0
           grind)
        | exact superpose b0e88 b0e35
        | exact resolve b0e35 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e88
      have b0e113 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ x) (M.op (σ y) (M.op X0 X0)) X1
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e116 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
        intro X0
        first
        | (have i₁ := b0e113 X0 x
           have i₂ := b0e43 (σ y) (M.op X0 X0) x
           grind)
        | exact superpose b0e43 b0e113
        | exact resolve b0e113 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e113
      have b0e123 : x = (σ x) := by
        first
        | (have i₁ := b0e116 x
           have i₂ := b0e78 x
           grind)
        | exact superpose b0e78 b0e116
        | exact resolve b0e116 b0e78
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78 b0e116
      have b0e130 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e123
           grind)
        | exact superpose b0e123 b0e18
        | exact resolve b0e18 b0e123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e123
      have b0e136 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e130
           have i₂ := b0e101 (σ y)
           grind)
        | exact superpose b0e101 b0e130
        | exact resolve b0e130 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101 b0e130
      have b0e139 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e136
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e136
        | exact resolve b0e136 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e136
      have b0e140 : False := by grind
      exact b0e140
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
        have b1e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e44
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e23
             grind)
          | exact resolve b1e47 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e51 : (σ y) = (σ (k x y)) := by
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
        have b1e52 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e51
          | exact resolve b1e51 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e51
        have b1e53 : False := by grind
        exact b1e53
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e27 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e12 y x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
             have i₂ := b2e12 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op X0 X1) X2
             have i₂ := b2e29 X0 X1
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 X1 : G, x = (M.op (M.op y (M.op X0 X0)) (M.op y (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x (M.op y (M.op X0 X0)) X1
             have i₂ := b2e27 X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e70 : ∀ X0 : G, x = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e67 X0 x
             have i₂ := b2e36 y (M.op X0 X0) x
             grind)
          | exact superpose b2e36 b2e67
          | exact resolve b2e67 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e67
        have b2e80 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 X0 X0
             have i₂ := b2e70 (M.op X0 X0)
             grind)
          | exact superpose b2e70 b2e12
          | exact resolve b2e12 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e89 : ∀ X0 : G, (M.op x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b2e29 X0 x
             have i₂ := b2e80 X0
             grind)
          | exact superpose b2e80 b2e29
          | exact resolve b2e29 b2e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e91 : ∀ X0 : G, X0 ≠ X0 ∨ x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b2e15 x X0
             have i₂ := b2e80 X0
             grind)
          | exact superpose b2e80 b2e15
          | (have j0 := b2e15 x X0
             grind)
          | (have r₁ := b2e15 x X0
             have r₂ := b2e80 X0
             grind)
          | exact resolve b2e15 b2e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e92 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have j0 := b2e91 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91
        have b2e109 : ∀ X0 : G, X0 ≠ X0 ∨ x = X0 ∨ x = (k X0 x) := by
          intro X0
          first
          | (have i₁ := b2e16 X0 x
             have i₂ := b2e89 X0
             grind)
          | exact superpose b2e89 b2e16
          | (have j0 := b2e16 X0 x
             grind)
          | (have r₁ := b2e16 X0 x
             have r₂ := b2e89 X0
             grind)
          | exact resolve b2e16 b2e89
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e89
        have b2e115 : ∀ X0 : G, x = (k X0 x) ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b2e109 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e109
        have b2e214 : ∀ X0 : G, (σ x) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e26 X0 x
             have i₂ := b2e92 (τ X0)
             grind)
          | exact superpose b2e92 b2e26
          | exact resolve b2e26 b2e92
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e92
        have b2e586 : x = (σ x) ∨ x = (σ x) := by
          first
          | (have i₁ := b2e214 x
             have i₂ := b2e115 (σ x)
             grind)
          | exact superpose b2e115 b2e214
          | (have j1 := b2e115 (σ x)
             grind)
          | exact resolve b2e214 b2e115
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e115 b2e214
        have b2e591 : x = (σ x) := by grind
        clear b2e586
        have b2e662 : (σ y) ≠ (M.op (σ y) x) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e591
             grind)
          | exact superpose b2e591 b2e21
          | exact resolve b2e21 b2e591
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e591
        have b2e681 : False := by grind
        exact b2e681
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
        have b3e55 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e58 : x = y ∨ y = (k x y) := by grind
        clear b3e55
        have b3e60 : y = (k x y) := by
          first
          | (have r₁ := b3e58
             have r₂ := b3e23
             grind)
          | exact resolve b3e58 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : x = y := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e29
          | exact resolve b3e29 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e60
        have b3e65 : False := by grind
        exact b3e65
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b4e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op x x) := by
            first
            | (have i₁ := b4e34 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e34
            | exact resolve b4e34 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e34 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (M.op X1 X1) X1
               have i₂ := b4e34 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X0 X1) X2
               have i₂ := b4e34 X0 X1
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : x = (M.op x y) := by
            first
            | (have i₁ := b4e34 x x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e34
            | exact resolve b4e34 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e132 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e41 X0 x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e41
            | exact resolve b4e41 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e41
          have b4e156 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 x y X0 X1
               have i₂ := b4e64
               grind)
            | exact superpose b4e64 b4e33
            | exact resolve b4e33 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e64
          have b4e200 : ∀ X0 : G, y = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e156 X0 x
               have i₂ := b4e42 x (M.op X0 X0) x
               grind)
            | exact superpose b4e42 b4e156
            | exact resolve b4e156 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e156
          have b4e371 : y = (σ y) := by
            first
            | (have i₁ := b4e200 (σ x)
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e200
            | exact resolve b4e200 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e200
          have b4e398 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e371
               grind)
            | exact superpose b4e371 b4e20
            | exact resolve b4e20 b4e371
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e371
          have b4e407 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e398
               have i₂ := b4e132 (σ x)
               grind)
            | exact superpose b4e132 b4e398
            | exact resolve b4e398 b4e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e398
          have b4e409 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e407
               have i₂ := b4e132 x
               grind)
            | exact superpose b4e132 b4e407
            | exact resolve b4e407 b4e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132 b4e407
          have b4e410 : False := by grind
          exact b4e410
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X0 (M.op X3 X3))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op (M.op X0 X1) (M.op X2 X2)) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b5e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op X0 X1) (M.op X2 X2)) = (k (M.op (M.op X0 X1) (M.op X2 X2)) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e16 (M.op (M.op X0 X1) (M.op X2 X2)) X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 (M.op (M.op X0 X1) (M.op X2 X2)) X1
               grind)
            | (have r₁ := b5e16 (M.op (M.op X0 X0) (M.op X2 X2)) X0
               have r₂ := b5e13 X0 X0 X2
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : y = (M.op x x) := by
            first
            | (have i₁ := b5e31 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e31 X1 (M.op X0 X1)
               have i₂ := b5e31 X0 X1
               grind)
            | exact superpose b5e31 b5e31
            | exact resolve b5e31 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X1 X1) X1
               have i₂ := b5e31 (M.op X0 (M.op X1 X1)) (M.op X1 X1)
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X2 X2))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 (M.op X0 X1) X2
               have i₂ := b5e31 X0 X1
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : x = (M.op x y) := by
            first
            | (have i₁ := b5e31 x x
               have i₂ := b5e33
               grind)
            | exact superpose b5e33 b5e31
            | exact resolve b5e31 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e33
          have b5e114 : ∀ X0 X1 : G, y = (M.op (M.op x (M.op X0 X0)) (M.op x (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 x y X0 X1
               have i₂ := b5e56
               grind)
            | exact superpose b5e56 b5e30
            | exact resolve b5e30 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e56
          have b5e148 : ∀ X0 : G, y = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e114 X0 x
               have i₂ := b5e38 x (M.op X0 X0) x
               grind)
            | exact superpose b5e38 b5e114
            | exact resolve b5e114 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e114
          have b5e172 : ∀ X0 : G, (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0 X0
               have i₂ := b5e148 X0
               grind)
            | exact superpose b5e148 b5e35
            | exact resolve b5e35 b5e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e196 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X1)) = (k (M.op (M.op X0 X0) (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have j0 := b5e32 X0 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e197 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e196 X0 x
               have i₂ := b5e37 (M.op X0 X0) x
               grind)
            | exact superpose b5e37 b5e196
            | exact resolve b5e196 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e196
          have b5e198 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b5e197 X0
               have i₂ := b5e148 X0
               grind)
            | exact superpose b5e148 b5e197
            | exact resolve b5e197 b5e148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e148 b5e197
          have b5e201 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e28 X0 y
               have i₂ := b5e198 (τ X0)
               grind)
            | exact superpose b5e198 b5e28
            | exact resolve b5e28 b5e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e198
          have b5e251 : ∀ X0 : G, X0 ≠ X0 ∨ y = X0 ∨ y = (k X0 y) := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e172 X0
               grind)
            | exact superpose b5e172 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e172 X0
               grind)
            | exact resolve b5e17 b5e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e262 : ∀ X0 : G, y = (k X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b5e251 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e251
          have b5e870 : y = (σ y) ∨ y = (σ y) := by
            first
            | (have i₁ := b5e201 y
               have i₂ := b5e262 (σ y)
               grind)
            | exact superpose b5e262 b5e201
            | (have j1 := b5e262 (σ y)
               grind)
            | exact resolve b5e201 b5e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e201 b5e262
          have b5e874 : y = (σ y) := by grind
          clear b5e870
          have b5e945 : (σ x) ≠ (M.op y (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e874
               grind)
            | exact superpose b5e874 b5e24
            | exact resolve b5e24 b5e874
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e874
          have b5e960 : False := by grind
          exact b5e960
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
        have b6e66 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
        have b6e68 : x = (M.op y x) ∨ y = (M.op y x) := by grind
        clear b6e66
        have b6e71 : y = (M.op y x) := by
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
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          clear b7e42
          have b7e47 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e25
               grind)
            | exact resolve b7e45 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e45
          have b7e49 : (σ y) = (σ (k x y)) := by
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
          have b7e52 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e14
            | exact resolve b7e14 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : y = (k x y) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e52
            | exact resolve b7e52 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e62 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e63 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b7e62
          have b7e65 : x = (M.op y x) := by
            first
            | (have r₁ := b7e63
               have r₂ := b7e21
               grind)
            | exact resolve b7e63 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : False := by grind
          exact b7e67
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e28 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 (M.op (M.op X0 X1) (M.op X0 X1))
               have i₂ := b8e13 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e28 X1 (M.op X0 X1)
               have i₂ := b8e28 X0 X1
               grind)
            | exact superpose b8e28 b8e28
            | exact resolve b8e28 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e251 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e49 x y
               grind)
            | exact superpose b8e49 b8e20
            | (have j1 := b8e49 x y
               grind)
            | exact resolve b8e20 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49
          have b8e1552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e251
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e251
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e251 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251
          have b8e1553 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e1552
          have b8e25341 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e31 (σ x) (σ y)
               have i₂ := b8e1553
               grind)
            | exact superpose b8e1553 b8e31
            | exact resolve b8e31 b8e1553
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1553
          have b8e25367 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e25341
               have r₂ := b8e23
               grind)
            | exact resolve b8e25341 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25341
          have b8e287376 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e28 (σ x) (σ y)
               have i₂ := b8e25367
               grind)
            | exact superpose b8e25367 b8e28
            | exact resolve b8e28 b8e25367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25367
          have b8e287383 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e287376
               have r₂ := b8e24
               grind)
            | exact resolve b8e287376 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e287376
          have b8e287392 : y = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e31 x y
               have i₂ := b8e287383
               grind)
            | exact superpose b8e287383 b8e31
            | exact resolve b8e31 b8e287383
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e287383
          have b8e287422 : x = (M.op x y) := by
            first
            | (have r₁ := b8e287392
               have r₂ := b8e21
               grind)
            | exact resolve b8e287392 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e287392
          have b8e287710 : x = (M.op y x) := by
            first
            | (have i₁ := b8e28 x y
               have i₂ := b8e287422
               grind)
            | exact superpose b8e287422 b8e28
            | exact resolve b8e28 b8e287422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28 b8e287422
          have b8e287753 : False := by grind
          exact b8e287753
