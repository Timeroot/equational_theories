import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation978`: `x = y ◇ ((z ◇ z) ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation978 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law978 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law978.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e13 y x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
               have i₂ := b4e13 X0 (M.op X1 X1) X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op (M.op X1 X1) y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x (M.op (M.op X0 X0) y) X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
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
          have b4e90 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e30 X2
               have i₂ := b4e35 X0 X1 (σ X2)
               grind)
            | exact superpose b4e35 b4e30
            | exact resolve b4e30 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X1 (M.op X1 X1)
               have i₂ := b4e35 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b4e35 b4e13
            | exact resolve b4e13 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e94 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
            intro X0 X2
            first
            | (have i₁ := b4e90 X0 x X2
               have i₂ := b4e91 x X0
               grind)
            | exact superpose b4e91 b4e90
            | exact resolve b4e90 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e260 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1
               have i₂ := b4e94 (σ X1) X0
               grind)
            | exact superpose b4e94 b4e30
            | exact resolve b4e30 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30
          have b4e264 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (M.op X1 X1)
               have i₂ := b4e94 X0 X1
               grind)
            | exact superpose b4e94 b4e14
            | exact resolve b4e14 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e323 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b4e332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e323
               have r₂ := b4e23
               grind)
            | exact resolve b4e323 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e323
          have b4e1160 : ∀ X0 X2 : G, (M.op X0 (M.op x (M.op X2 X0))) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b4e13 X2 X0 (M.op (M.op x x) y)
               have i₂ := b4e36 x x
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1180 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e260 X0 (M.op (M.op x x) y)
               have i₂ := b4e36 x x
               grind)
            | exact superpose b4e36 b4e260
            | exact resolve b4e260 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e260
          have b4e1181 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
            intro X0
            first
            | (have i₁ := b4e264 (M.op (M.op x x) y) X0
               have i₂ := b4e36 x x
               grind)
            | exact superpose b4e36 b4e264
            | exact resolve b4e264 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e264
          have b4e1194 : (σ x) = (σ (τ x)) := by
            first
            | (have i₁ := b4e1180 x
               have i₂ := b4e1181 x
               grind)
            | exact superpose b4e1181 b4e1180
            | exact resolve b4e1180 b4e1181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1180 b4e1181
          have b4e1226 : x = (σ x) := by
            first
            | (have i₁ := b4e1194
               have i₂ := b4e15 x
               grind)
            | exact superpose b4e15 b4e1194
            | exact resolve b4e1194 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1194
          have b4e1256 : x ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e1226
               grind)
            | exact superpose b4e1226 b4e23
            | exact resolve b4e23 b4e1226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e7325 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e332
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e332
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e332
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e332
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e332 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e332
          have b4e7326 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e7325
          have b4e7327 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e7326
               have r₂ := b4e21
               grind)
            | exact resolve b4e7326 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7326
          have b4e7328 : x = (M.op x (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e7327
               have i₂ := b4e1226
               grind)
            | exact superpose b4e1226 b4e7327
            | exact resolve b4e7327 b4e1226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1226 b4e7327
          have b4e22521 : x = (M.op (σ y) (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1160 (σ y) x
               have i₂ := b4e7328
               grind)
            | exact superpose b4e7328 b4e1160
            | exact resolve b4e1160 b4e7328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7328
          have b4e22526 : x = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e22521
               have i₂ := b4e91 x (σ y)
               grind)
            | exact superpose b4e91 b4e22521
            | exact resolve b4e22521 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22521
          have b4e22545 : x = (M.op x y) := by
            first
            | (have r₁ := b4e22526
               have r₂ := b4e1256
               grind)
            | exact resolve b4e22526 b4e1256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1256 b4e22526
          have b4e22580 : x = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b4e1160 y x
               have i₂ := b4e22545
               grind)
            | exact superpose b4e22545 b4e1160
            | exact resolve b4e1160 b4e22545
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1160 b4e22545
          have b4e22586 : x = y := by
            first
            | (have i₁ := b4e22580
               have i₂ := b4e91 x y
               grind)
            | exact superpose b4e91 b4e22580
            | exact resolve b4e22580 b4e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91 b4e22580
          have b4e22605 : False := by grind
          exact b4e22605
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
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
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 : G, y = (M.op x (M.op (M.op X0 X0) y)) := by
            intro X0
            first
            | (have i₁ := b5e13 y x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
               have i₂ := b5e13 X0 (M.op X1 X1) X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X0) y) (M.op (M.op X1 X1) y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x (M.op (M.op X0 X0) y) X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e85 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e30 X2
               have i₂ := b5e34 X0 X1 (σ X2)
               grind)
            | exact superpose b5e34 b5e30
            | exact resolve b5e30 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X1 (M.op X1 X1)
               have i₂ := b5e34 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e89 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
            intro X0 X2
            first
            | (have i₁ := b5e85 X0 x X2
               have i₂ := b5e86 x X0
               grind)
            | exact superpose b5e86 b5e85
            | exact resolve b5e85 b5e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e246 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 X1
               have i₂ := b5e89 (σ X1) X0
               grind)
            | exact superpose b5e89 b5e30
            | exact resolve b5e30 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e250 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (M.op X1 X1)
               have i₂ := b5e89 X0 X1
               grind)
            | exact superpose b5e89 b5e14
            | exact resolve b5e14 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e1035 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e86 (M.op (M.op x x) y) X0
               have i₂ := b5e35 x x
               grind)
            | exact superpose b5e35 b5e86
            | exact resolve b5e86 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e1042 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e246 X0 (M.op (M.op x x) y)
               have i₂ := b5e35 x x
               grind)
            | exact superpose b5e35 b5e246
            | exact resolve b5e246 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e246
          have b5e1043 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
            intro X0
            first
            | (have i₁ := b5e250 (M.op (M.op x x) y) X0
               have i₂ := b5e35 x x
               grind)
            | exact superpose b5e35 b5e250
            | exact resolve b5e250 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e250
          have b5e1054 : (σ x) = (σ (τ x)) := by
            first
            | (have i₁ := b5e1042 x
               have i₂ := b5e1043 x
               grind)
            | exact superpose b5e1043 b5e1042
            | exact resolve b5e1042 b5e1043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1042 b5e1043
          have b5e1084 : x = (σ x) := by
            first
            | (have i₁ := b5e1054
               have i₂ := b5e15 x
               grind)
            | exact superpose b5e15 b5e1054
            | exact resolve b5e1054 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1054
          have b5e1110 : (σ y) ≠ (M.op (σ y) x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1084
               grind)
            | exact superpose b5e1084 b5e24
            | exact resolve b5e24 b5e1084
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1084
          have b5e1120 : False := by grind
          exact b5e1120
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
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X2) (M.op X0 X1))) = X0 := by
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
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X3 X3) X0)) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op (M.op X1 X1) (M.op X0 X2)) X3
               have i₂ := b8e13 X0 X2 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X1)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X2 X2) (M.op X0 (M.op X1 X1)) X1
               have i₂ := b8e13 X0 (M.op X1 X1) X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b8e59 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (k X1 (τ X0))
               have i₂ := b8e27 X0 X1
               grind)
            | exact superpose b8e27 b8e30
            | exact resolve b8e30 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e69 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 x x X0
               have i₂ := b8e33 x x X1
               grind)
            | exact superpose b8e33 b8e33
            | exact resolve b8e33 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e30 X2
               have i₂ := b8e33 X0 X1 (σ X2)
               grind)
            | exact superpose b8e33 b8e30
            | exact resolve b8e30 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e74 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X1 (M.op X1 X1)
               have i₂ := b8e33 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e77 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (M.op X2 X2)) := by
            intro X0 X2
            first
            | (have i₁ := b8e73 X0 x X2
               have i₂ := b8e74 x X0
               grind)
            | exact superpose b8e74 b8e73
            | exact resolve b8e73 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e124 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op (M.op X5 X5) (M.op (M.op X2 X2) (M.op X3 X0)))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e32 (M.op (M.op X2 X2) (M.op X3 X0)) X1 (M.op (M.op X4 X4) X3) X5
               have i₂ := b8e32 X3 X2 X0 X4
               grind)
            | exact superpose b8e32 b8e32
            | exact resolve b8e32 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e129 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X2 X2) X1)) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X1 X1 X1 X2
               have i₂ := b8e69 (M.op X1 X1) X0
               grind)
            | (have i₁ := b8e32 X1 X1 X1 X2
               have i₂ := b8e69 X0 (M.op X1 X1)
               grind)
            | exact superpose b8e69 b8e32
            | exact resolve b8e32 b8e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e69
          have b8e146 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) (M.op X2 X0)) = (M.op (M.op (M.op X1 X1) X2) (M.op (M.op X3 X3) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 (M.op (M.op X4 X4) (M.op X2 X0)) (M.op (M.op X1 X1) X2) X3
               have i₂ := b8e32 X2 X4 X0 X1
               grind)
            | exact superpose b8e32 b8e13
            | exact resolve b8e13 b8e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e156 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X4 X4) X3) = (M.op (M.op (M.op X1 X1) X0) (M.op X3 X0)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e124 X0 X1 x X3 X4 x
               have i₂ := b8e129 x (M.op X3 X0) x
               grind)
            | exact superpose b8e129 b8e124
            | exact resolve b8e124 b8e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e124
          have b8e231 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op X1 X1)
               have i₂ := b8e77 X0 X1
               grind)
            | exact superpose b8e77 b8e14
            | exact resolve b8e14 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e248 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e255 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e248
               have r₂ := b8e23
               grind)
            | exact resolve b8e248 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e248
          have b8e346 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X1 X1
               have i₂ := b8e231 X0 (M.op X1 X1)
               grind)
            | exact superpose b8e231 b8e13
            | exact resolve b8e13 b8e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e231
          have b8e2708 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) (M.op (M.op X3 X3) (M.op (M.op X0 X0) X1))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 (M.op (M.op X4 X4) X2) (M.op X1 X2) X3
               have i₂ := b8e156 X2 X4 X1 X0
               grind)
            | exact superpose b8e156 b8e13
            | exact resolve b8e13 b8e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156
          have b8e2709 : ∀ X1 X2 X4 : G, (M.op (M.op X4 X4) X2) = (M.op (M.op X1 X2) X1) := by
            intro X1 X2 X4
            first
            | (have i₁ := b8e2708 x X1 X2 x X4
               have i₂ := b8e129 x X1 x
               grind)
            | exact superpose b8e129 b8e2708
            | exact resolve b8e2708 b8e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129 b8e2708
          have b8e3752 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e255
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e255
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e255
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e255
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e255 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e255
          have b8e3753 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e3752
          have b8e3754 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e3753
               have r₂ := b8e21
               grind)
            | exact resolve b8e3753 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3753
          have b8e4715 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X2) X1)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X1 x X2 x
               have i₂ := b8e146 X1 x (M.op X1 X2) x X0
               grind)
            | (have i₁ := b8e32 X0 X0 X0 x
               have i₂ := b8e146 X0 X1 (M.op x x) x (M.op X0 X0)
               grind)
            | exact superpose b8e146 b8e32
            | exact resolve b8e32 b8e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32 b8e146
          have b8e7015 : ∀ X0 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X2 X0) X2)) X3) = X0 := by
            intro X0 X2 X3
            first
            | (have i₁ := b8e2709 X3 (M.op (M.op X2 X0) X2) x
               have i₂ := b8e4715 x X2 X0
               grind)
            | exact superpose b8e4715 b8e2709
            | exact resolve b8e2709 b8e4715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2709 b8e4715
          have b8e14126 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) X0) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e7015 (σ y) (σ x) X0
               have i₂ := b8e3754
               grind)
            | exact superpose b8e3754 b8e7015
            | exact resolve b8e7015 b8e3754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3754
          have b8e14128 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e14126 X0
               have i₂ := b8e74 (σ x) X0
               grind)
            | exact superpose b8e74 b8e14126
            | exact resolve b8e14126 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14126
          have b8e15432 : ∀ X0 : G, (M.op X0 (τ (σ y))) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e346 x X0
               have i₂ := b8e14128 x
               grind)
            | exact superpose b8e14128 b8e346
            | exact resolve b8e346 b8e14128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e346 b8e14128
          have b8e15607 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e15432 X0
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e15432
            | exact resolve b8e15432 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15432
          have b8e15808 : x ≠ x ∨ x = (M.op x y) := by
            first
            | (have j0 := b8e15607 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15607
          have b8e15809 : x = (M.op x y) := by grind
          clear b8e15808
          have b8e15929 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b8e7015 y x X0
               have i₂ := b8e15809
               grind)
            | exact superpose b8e15809 b8e7015
            | exact resolve b8e7015 b8e15809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7015 b8e15809
          have b8e15931 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b8e15929 X0
               have i₂ := b8e74 x X0
               grind)
            | exact superpose b8e74 b8e15929
            | exact resolve b8e15929 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74 b8e15929
          have b8e16276 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 X0 X0
               have i₂ := b8e15931 (M.op X0 X0)
               grind)
            | exact superpose b8e15931 b8e13
            | exact resolve b8e13 b8e15931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e16305 : ∀ X0 X1 : G, (σ y) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e59 X0 X1
               have i₂ := b8e15931 (k X0 (τ X1))
               grind)
            | exact superpose b8e15931 b8e59
            | exact resolve b8e59 b8e15931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e16306 : y = (σ y) := by
            first
            | (have i₁ := b8e16305 x x
               have i₂ := b8e15931 (k (σ x) x)
               grind)
            | exact superpose b8e15931 b8e16305
            | exact resolve b8e16305 b8e15931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15931 b8e16305
          have b8e16722 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e16306
               grind)
            | exact superpose b8e16306 b8e20
            | exact resolve b8e20 b8e16306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16306
          have b8e16763 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e16722
               have i₂ := b8e16276 (σ x)
               grind)
            | exact superpose b8e16276 b8e16722
            | exact resolve b8e16722 b8e16276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16722
          have b8e16768 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e16763
               have i₂ := b8e16276 x
               grind)
            | exact superpose b8e16276 b8e16763
            | exact resolve b8e16763 b8e16276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16276 b8e16763
          have b8e16769 : False := by grind
          exact b8e16769
