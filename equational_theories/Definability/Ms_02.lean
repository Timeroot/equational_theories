import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4407`: `x ◇ (x ◇ y) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation4407 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4407 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4407.models_iff G M).mp hM
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
      have b0e66 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e69 : False := by grind
      exact b0e69
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 : G, (M.op y (M.op y x)) = (M.op y X0) := by
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
          have b5e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X0) X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X1 X0) X1 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X1 (M.op (M.op X1 X2) X0)
               have i₂ := b5e13 (M.op X1 X2) X0 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e45 X0 X1 X2 X3
               have i₂ := b5e13 X0 X1 (M.op (M.op X1 X0) X1)
               grind)
            | exact superpose b5e13 b5e45
            | exact resolve b5e45 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e52 : ∀ X0 X1 : G, (M.op (M.op y (M.op y x)) X1) = (M.op X0 (M.op X0 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e44 X0
               grind)
            | (have i₁ := b5e13 (M.op y x) y x
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e13
            | exact resolve b5e13 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e53 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e52 X0 x
               have i₂ := b5e47 y y x x
               grind)
            | exact superpose b5e47 b5e52
            | exact resolve b5e52 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e52
          have b5e55 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e53 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e53
            | exact resolve b5e53 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e57 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e55 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e55
            | exact resolve b5e55 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e117 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X0 y) X1
               have i₂ := b5e57 X0
               grind)
            | exact superpose b5e57 b5e13
            | exact resolve b5e13 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e118 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X0) y)
               have i₂ := b5e57 (M.op X1 X0)
               grind)
            | exact superpose b5e57 b5e13
            | exact resolve b5e13 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e121 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e117 X0 x
               have i₂ := b5e48 X0 y X0 x
               grind)
            | exact superpose b5e48 b5e117
            | exact resolve b5e117 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e117
          have b5e124 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e121 X0
               have i₂ := b5e57 X0
               grind)
            | exact superpose b5e57 b5e121
            | exact resolve b5e121 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e121
          have b5e177 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e57 (M.op X0 X1)
               have i₂ := b5e42 X0 X1 (M.op (M.op X0 X1) y) X2
               grind)
            | (have i₁ := b5e57 (M.op X0 X1)
               have i₂ := b5e42 X0 X1 X2 (M.op (M.op X0 X1) y)
               grind)
            | exact superpose b5e42 b5e57
            | exact resolve b5e57 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e57
          have b5e876 : ∀ X0 X1 : G, y = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e177 (σ X0) (σ X0) X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e177
            | exact resolve b5e177 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e177
          have b5e1396 : ∀ X0 : G, y = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e31 (M.op X0 X0)
               have i₂ := b5e876 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e876 b5e31
            | exact resolve b5e31 b5e876
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e876
          have b5e1434 : ∀ X0 : G, y = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e1396 X0
               have i₂ := b5e13 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e13 b5e1396
            | exact resolve b5e1396 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1396
          have b5e1447 : y = (σ y) := by
            first
            | (have i₁ := b5e1434 x
               have i₂ := b5e118 x x
               grind)
            | exact superpose b5e118 b5e1434
            | exact resolve b5e1434 b5e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e118 b5e1434
          have b5e1559 : y ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1447
               grind)
            | exact superpose b5e1447 b5e24
            | exact resolve b5e24 b5e1447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1447
          have b5e1565 : False := by grind
          exact b5e1565
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
          have b7e52 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e55 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e52
          have b7e56 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e23
               grind)
            | exact resolve b7e55 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e57 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e56
            | exact resolve b7e56 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e67 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e57
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e57 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e68 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e26
               grind)
            | exact resolve b7e67 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e67
          have b7e69 : x = y := by
            first
            | (have r₁ := b7e68
               have r₂ := b7e22
               grind)
            | exact resolve b7e68 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e70 : False := by grind
          exact b7e70
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
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e883 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e63 x y
               grind)
            | exact superpose b8e63 b8e20
            | (have j1 := b8e63 x y
               grind)
            | exact resolve b8e20 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e905 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e883
               have r₂ := b8e24
               grind)
            | exact resolve b8e883 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e883
          have b8e910 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e905
               have r₂ := b8e23
               grind)
            | exact resolve b8e905 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e905
          have b8e913 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e910
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e910
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e910
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e910
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e910 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e910
          have b8e914 : y = (M.op x y) ∨ x = y := by grind
          clear b8e913
          have b8e915 : x = y := by
            first
            | (have r₁ := b8e914
               have r₂ := b8e22
               grind)
            | exact resolve b8e914 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e914
          have b8e916 : False := by grind
          exact b8e916

/-- `Equation4410`: `x ◇ (x ◇ y) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4410 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4410 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4410.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
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
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
      have b0e28 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
        intro X0
        grind
      clear b0e25
      have b0e32 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e28 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e28
        | exact resolve b0e28 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 x)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (k (M.op X2 X2) X0) ∨ (M.op X1 (M.op X1 X2)) = X0 ∨ (M.op (M.op X2 X2) X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op X2 X2)
           have i₂ := b0e16 (M.op X2 X2) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X1 X1) X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X2 X2) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e83 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X1 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op (M.op X2 X2) x)
           have i₂ := b0e41 (M.op X2 X2) X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e85 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e36 x
           have i₂ := b0e41 X0 x
           grind)
        | (have i₁ := b0e36 (M.op y x)
           have i₂ := b0e41 y x
           grind)
        | exact superpose b0e41 b0e36
        | exact resolve b0e36 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e88 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op X1 X2)) := by
        intro X1 X2
        first
        | (have i₁ := b0e83 x X1 X2
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e83
        | exact resolve b0e83 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e107 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      clear b0e26
      have b0e125 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X1
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e35
        | exact resolve b0e35 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e130 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e18
        | exact resolve b0e18 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e135 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
      have b0e139 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e85 (σ y)
           have i₂ := b0e35 (M.op (σ y) x)
           grind)
        | exact superpose b0e35 b0e85
        | exact resolve b0e85 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e145 : (σ y) = (k (σ y) (M.op x y)) := by
        first
        | (have i₁ := b0e135
           have i₂ := b0e139
           grind)
        | exact superpose b0e139 b0e135
        | exact resolve b0e135 b0e139
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135 b0e139
      have b0e321 : ∀ X0 : G, (M.op x y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e85 (σ y)
           have i₂ := b0e125 (M.op (σ y) x) X0
           grind)
        | (have i₁ := b0e85 (σ y)
           have i₂ := b0e125 X0 (M.op (σ y) x)
           grind)
        | exact superpose b0e125 b0e85
        | exact resolve b0e85 b0e125
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125
      have b0e678 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e130 (M.op (σ y) x)
           have i₂ := b0e85 (σ y)
           grind)
        | exact superpose b0e85 b0e130
        | exact resolve b0e130 b0e85
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85 b0e130
      have b0e3466 : (k y (τ (M.op x y))) = (τ (σ y)) := by
        first
        | (have i₁ := b0e107 y (M.op x y)
           have i₂ := b0e145
           grind)
        | exact superpose b0e145 b0e107
        | exact resolve b0e107 b0e145
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107 b0e145
      have b0e3486 : y = (k y (τ (M.op x y))) := by
        first
        | (have i₁ := b0e3466
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e3466
        | exact resolve b0e3466 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3466
      have b0e3890 : ∀ X0 X1 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X1 (M.op X1 (σ x))) = X0 ∨ (M.op (σ y) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e67 X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e67
        | (have j0 := b0e67 X0 X1 (σ x)
           grind)
        | exact resolve b0e67 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e3935 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op y X0) = (k y X0) ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e67 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e67
        | exact resolve b0e67 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67
      have b0e4095 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op x y) = X0 ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3935 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e3935
        | (have j0 := b0e3935 X0
           grind)
        | exact resolve b0e3935 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3935
      have b0e4137 : ∀ X0 X1 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op X1 (M.op X1 (σ x))) = X0 ∨ (M.op (σ y) X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e3890 X0 X1
           have i₂ := b0e321 X0
           grind)
        | exact superpose b0e321 b0e3890
        | (have j0 := b0e3890 X0 X1
           grind)
        | exact resolve b0e3890 b0e321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3890
      have b0e4217 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = (k y X0) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e4095 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e4095
        | (have j0 := b0e4095 X0
           grind)
        | exact resolve b0e4095 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4095
      have b0e4218 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have j0 := b0e4217 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4217
      have b0e4259 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = (k (σ y) X0) ∨ (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e4137 X0 x
           have i₂ := b0e88 x (σ x)
           grind)
        | exact superpose b0e88 b0e4137
        | (have j0 := b0e4137 X0 x
           grind)
        | exact resolve b0e4137 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88 b0e4137
      have b0e4325 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op x y) = X0 ∨ (M.op x y) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e4259 X0
           have i₂ := b0e321 X0
           grind)
        | exact superpose b0e321 b0e4259
        | (have j0 := b0e4259 X0
           grind)
        | exact resolve b0e4259 b0e321
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e321 b0e4259
      have b0e4326 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have j0 := b0e4325 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4325
      have b0e5504 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
        first
        | (have i₁ := b0e32 (σ y)
           have i₂ := b0e4326 (σ (M.op (τ (σ y)) (τ (σ y))))
           grind)
        | exact superpose b0e4326 b0e32
        | (have j1 := b0e4326 (σ y)
           grind)
        | exact resolve b0e32 b0e4326
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e4326
      have b0e5507 : (M.op x y) = (σ (M.op y y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e5504
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e5504
        | exact resolve b0e5504 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5504
      have b0e5510 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e5507
           have i₂ := b0e36 y
           grind)
        | exact superpose b0e36 b0e5507
        | exact resolve b0e5507 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e5507
      have b0e5512 : (M.op x y) = (σ y) := by
        first
        | (have r₁ := b0e5510
           have r₂ := b0e678
           grind)
        | exact resolve b0e5510 b0e678
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5510
      have b0e5596 : y = (k y (τ (σ y))) := by
        first
        | (have i₁ := b0e3486
           have i₂ := b0e5512
           grind)
        | exact superpose b0e5512 b0e3486
        | exact resolve b0e3486 b0e5512
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3486
      have b0e5617 : y = (k y y) := by
        first
        | (have i₁ := b0e5596
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e5596
        | exact resolve b0e5596 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5596
      have b0e5657 : y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4218 y
           have i₂ := b0e5617
           grind)
        | exact superpose b0e5617 b0e4218
        | (have j0 := b0e4218 y
           grind)
        | exact resolve b0e4218 b0e5617
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4218 b0e5617
      have b0e5666 : y = (M.op x y) := by grind
      clear b0e5657
      have b0e5912 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e678
           have i₂ := b0e5666
           grind)
        | exact superpose b0e5666 b0e678
        | exact resolve b0e678 b0e5666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e678
      have b0e5918 : y = (σ y) := by
        first
        | (have i₁ := b0e5512
           have i₂ := b0e5666
           grind)
        | exact superpose b0e5666 b0e5512
        | exact resolve b0e5512 b0e5666
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5512 b0e5666
      have b0e5935 : False := by grind
      exact b0e5935
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
        have b1e31 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 x)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1
          grind
        have b1e79 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2 (M.op (M.op X2 X2) x)
             have i₂ := b1e35 (M.op X2 X2) X0
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e84 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b1e79 x X1 X2
             have i₂ := b1e31 x
             grind)
          | exact superpose b1e31 b1e79
          | exact resolve b1e79 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e79
        have b1e134 : (M.op x y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e84 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e84
          | exact resolve b1e84 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e147 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b1e134
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e134
          | exact resolve b1e134 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e134
        have b1e663 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op X0 y))) := by
          intro X0
          first
          | (have i₁ := b1e38 X0 y
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e38
          | exact resolve b1e38 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e728 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b1e663 x
             have i₂ := b1e84 x y
             grind)
          | exact superpose b1e84 b1e663
          | exact resolve b1e663 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84 b1e663
        have b1e759 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e728
             have i₂ := b1e147
             grind)
          | exact superpose b1e147 b1e728
          | exact resolve b1e728 b1e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147 b1e728
        have b1e772 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e759
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e759
          | exact resolve b1e759 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e759
        have b1e1120 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e772
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e772
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e772 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e772
        have b1e1124 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e1120
        have b1e1128 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e1124
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e1124
          | exact resolve b1e1124 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1124
        have b1e1129 : y = (M.op y y) := by
          first
          | (have r₁ := b1e1128
             have r₂ := b1e24
             grind)
          | exact resolve b1e1128 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1128
        have b1e1130 : y = (M.op x y) := by
          first
          | (have i₁ := b1e1129
             have i₂ := b1e31 y
             grind)
          | exact superpose b1e31 b1e1129
          | exact resolve b1e1129 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e1129
        have b1e2226 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e1130
             grind)
          | exact superpose b1e1130 b1e24
          | exact resolve b1e24 b1e1130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e1130
        have b1e2236 : False := by grind
        exact b1e2236
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
        have b2e27 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 x)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e72 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2 (M.op (M.op X2 X2) x)
             have i₂ := b2e32 (M.op X2 X2) X0
             grind)
          | exact superpose b2e32 b2e12
          | exact resolve b2e12 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32
        have b2e77 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b2e72 x X1 X2
             have i₂ := b2e27 x
             grind)
          | exact superpose b2e27 b2e72
          | exact resolve b2e72 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e72
        have b2e118 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e1393 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e118
        have b2e1406 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1393 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1393
          | exact resolve b2e1393 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1393
        have b2e2501 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e2502 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2501
             have r₂ := b2e22
             grind)
          | exact resolve b2e2501 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2501
        have b2e2503 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2502
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2502
          | exact resolve b2e2502 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2502
        have b2e2504 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e2503
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e2503
          | exact resolve b2e2503 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2503
        have b2e2508 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2504
             grind)
          | exact superpose b2e2504 b2e22
          | exact resolve b2e22 b2e2504
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2520 : (M.op x y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e77 (σ x) (σ y)
             have i₂ := b2e2504
             grind)
          | exact superpose b2e2504 b2e77
          | exact resolve b2e77 b2e2504
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e2504
        have b2e3261 : x = (k x (τ (M.op x y))) := by
          first
          | (have i₁ := b2e1406 x
             have i₂ := b2e2520
             grind)
          | exact superpose b2e2520 b2e1406
          | exact resolve b2e1406 b2e2520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1406
        have b2e3782 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e49 x x
             grind)
          | exact superpose b2e49 b2e21
          | (have j1 := b2e49 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e49 x y
             grind)
          | exact resolve b2e21 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e3877 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e3782
        have b2e3928 : (σ y) ≠ (σ (k x x)) ∨ (M.op x y) = (σ x) := by
          first
          | (have i₁ := b2e3877
             have i₂ := b2e2520
             grind)
          | exact superpose b2e2520 b2e3877
          | exact resolve b2e3877 b2e2520
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2520 b2e3877
        have b2e4591 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e3928
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e3928
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e3928 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3928
        have b2e4592 : (σ y) ≠ (σ (M.op x x)) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by grind
        clear b2e4591
        have b2e4594 : (σ y) ≠ (σ y) ∨ (M.op x y) = (σ x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4592
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4592
          | exact resolve b2e4592 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4592
        have b2e4595 : (M.op x y) = (σ x) ∨ x = (M.op x x) := by grind
        clear b2e4594
        have b2e4604 : (M.op x y) = (σ x) ∨ x = y := by
          first
          | (have i₁ := b2e4595
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4595
          | exact resolve b2e4595 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4595
        have b2e4620 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3261
             have i₂ := b2e4604
             grind)
          | exact superpose b2e4604 b2e3261
          | exact resolve b2e3261 b2e4604
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3261 b2e4604
        have b2e4642 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e4620
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e4620
          | exact resolve b2e4620 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4620
        have b2e4718 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e4642
             grind)
          | exact superpose b2e4642 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e4642
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4642
        have b2e4719 : x = (M.op x x) ∨ x = y := by grind
        clear b2e4718
        have b2e4730 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e4719
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e4719
          | exact resolve b2e4719 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4719
        have b2e4731 : x = y := by grind
        clear b2e4730
        have b2e5112 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e2508
             have i₂ := b2e4731
             grind)
          | exact superpose b2e4731 b2e2508
          | exact resolve b2e2508 b2e4731
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2508 b2e4731
        have b2e5117 : False := by grind
        exact b2e5117
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b3e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e36 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b3e29
        have b3e40 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e36 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e36
          | exact resolve b3e36 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e43 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e12 X2 X1 x
             grind)
          | (have i₁ := b3e12 X0 X1 (M.op (M.op X1 X1) X1)
             have i₂ := b3e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e43 X1
             have i₂ := b3e43 X0
             grind)
          | exact superpose b3e43 b3e43
          | exact resolve b3e43 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e24
             have i₂ := b3e43 X0
             grind)
          | exact superpose b3e43 b3e24
          | exact resolve b3e24 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e73 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 X1
             have i₂ := b3e43 (M.op (σ y) X0)
             grind)
          | exact superpose b3e43 b3e12
          | exact resolve b3e12 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e288 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e48 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e48
          | exact resolve b3e48 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e327 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e288 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e288
          | exact resolve b3e288 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e288
        have b3e363 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X0 y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (M.op X0 y) X1
             have i₂ := b3e327 X0
             grind)
          | exact superpose b3e327 b3e12
          | exact resolve b3e12 b3e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e369 : ∀ X0 : G, y = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e64 (M.op (σ y) y) X0
             have i₂ := b3e327 (σ y)
             grind)
          | exact superpose b3e327 b3e64
          | exact resolve b3e64 b3e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e370 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e66 (M.op (σ y) y)
             have i₂ := b3e327 (σ y)
             grind)
          | exact superpose b3e327 b3e66
          | exact resolve b3e66 b3e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e371 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e43 (M.op (σ y) y)
             have i₂ := b3e327 (σ y)
             grind)
          | exact superpose b3e327 b3e43
          | exact resolve b3e43 b3e327
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e327
        have b3e373 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e363 X0 x
             have i₂ := b3e73 (M.op X0 y) x
             grind)
          | exact superpose b3e73 b3e363
          | exact resolve b3e363 b3e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73 b3e363
        have b3e376 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e373 X0
             have i₂ := b3e371
             grind)
          | exact superpose b3e371 b3e373
          | exact resolve b3e373 b3e371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e371 b3e373
        have b3e1860 : ∀ X0 : G, y = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e17 (σ y) X0
             have i₂ := b3e369 (σ y)
             grind)
          | exact superpose b3e369 b3e17
          | (have j0 := b3e17 (σ y) X0
             grind)
          | exact resolve b3e17 b3e369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e1906 : ∀ X0 : G, y = (k (σ y) X0) ∨ y = X0 ∨ (M.op (σ y) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e1860 X0
             have i₂ := b3e369 X0
             grind)
          | exact superpose b3e369 b3e1860
          | (have j0 := b3e1860 X0
             grind)
          | exact resolve b3e1860 b3e369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1860
        have b3e1918 : ∀ X0 : G, y = X0 ∨ y = (k (σ y) X0) ∨ y = X0 := by
          intro X0
          first
          | (have i₁ := b3e1906 X0
             have i₂ := b3e369 X0
             grind)
          | exact superpose b3e369 b3e1906
          | (have j0 := b3e1906 X0
             grind)
          | exact resolve b3e1906 b3e369
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e369 b3e1906
        have b3e1919 : ∀ X0 : G, y = (k (σ y) X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e1918 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1918
        have b3e4301 : y = (σ y) ∨ y = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
          first
          | (have i₁ := b3e1919 (σ (M.op (τ (σ y)) (τ (σ y))))
             have i₂ := b3e40 (σ y)
             grind)
          | exact superpose b3e40 b3e1919
          | (have j0 := b3e1919 (σ y)
             grind)
          | exact resolve b3e1919 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e1919
        have b3e4304 : y = (σ (M.op (τ (σ y)) (τ (σ y)))) := by
          first
          | (have r₁ := b3e4301
             have r₂ := b3e370
             grind)
          | exact resolve b3e4301 b3e370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4301
        have b3e4318 : y = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e4304
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4304
          | exact resolve b3e4304 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4304
        have b3e4325 : y = (σ y) := by
          first
          | (have i₁ := b3e4318
             have i₂ := b3e376 y
             grind)
          | exact superpose b3e376 b3e4318
          | exact resolve b3e4318 b3e376
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e376 b3e4318
        have b3e4333 : False := by grind
        exact b3e4333
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
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
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b5e37 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e13 x X0 X3
               have i₂ := b5e13 x X0 X1
               grind)
            | (have i₁ := b5e13 (M.op X1 X1) X1 x
               have i₂ := b5e13 X0 X1 (M.op (M.op X1 X1) X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e13 X2 X1 x
               grind)
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X1) X1)
               have i₂ := b5e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) X1) = (M.op X2 (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X3 (M.op (M.op X3 X3) X0)
               have i₂ := b5e13 (M.op X3 X3) X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e51 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e54 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e51
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e54
               have r₂ := b5e21
               grind)
            | exact resolve b5e54 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e136 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e40 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e162 : ∀ X0 : G, y = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e136 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e136
            | exact resolve b5e136 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e136
          have b5e180 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) (M.op X0 y)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (M.op X0 y) X1
               have i₂ := b5e162 X0
               grind)
            | exact superpose b5e162 b5e13
            | exact resolve b5e13 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e182 : ∀ X0 X1 : G, y = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 X0 (M.op (M.op X0 X0) y) X1
               have i₂ := b5e162 (M.op X0 X0)
               grind)
            | exact superpose b5e162 b5e37
            | exact resolve b5e37 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e183 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op (M.op X1 X1) y)
               have i₂ := b5e162 (M.op X1 X1)
               grind)
            | exact superpose b5e162 b5e13
            | exact resolve b5e13 b5e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e162
          have b5e184 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e180 X0 x
               have i₂ := b5e182 (M.op X0 y) x
               grind)
            | exact superpose b5e182 b5e180
            | exact resolve b5e180 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e225 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = X3 ∨ (M.op (M.op X2 X2) X3) = (k (M.op X2 X2) X3) ∨ (M.op (M.op X2 X2) X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e18 (M.op X2 X2) X3
               have i₂ := b5e41 X2 (M.op X2 X2) X0 X1
               grind)
            | exact superpose b5e41 b5e18
            | (have j0 := b5e18 (M.op X2 X2) X3
               grind)
            | exact resolve b5e18 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e255 : ∀ X2 X3 : G, y = X3 ∨ (M.op (M.op X2 X2) X3) = (k (M.op X2 X2) X3) ∨ (M.op (M.op X2 X2) X3) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b5e225 x x X2 X3
               have i₂ := b5e183 x x
               grind)
            | exact superpose b5e183 b5e225
            | (have j0 := b5e225 x x X2 X3
               grind)
            | exact resolve b5e225 b5e183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e225
          have b5e273 : ∀ X2 X3 : G, y = (k (M.op X2 X2) X3) ∨ y = X3 ∨ (M.op (M.op X2 X2) X3) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b5e255 X2 X3
               have i₂ := b5e182 X2 X3
               grind)
            | exact superpose b5e182 b5e255
            | (have j0 := b5e255 X2 X3
               grind)
            | exact resolve b5e255 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e255
          have b5e283 : ∀ X2 X3 : G, y = X3 ∨ y = (k (M.op X2 X2) X3) ∨ y = X3 := by
            intro X2 X3
            first
            | (have i₁ := b5e273 X2 X3
               have i₂ := b5e182 X2 X3
               grind)
            | exact superpose b5e182 b5e273
            | (have j0 := b5e273 X2 X3
               grind)
            | exact resolve b5e273 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182 b5e273
          have b5e284 : ∀ X2 X3 : G, y = (k (M.op X2 X2) X3) ∨ y = X3 := by
            intro X2 X3
            first
            | (have j0 := b5e283 X2 X3
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e283
          have b5e383 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e184 X0
               grind)
            | exact superpose b5e184 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e184 X0
               grind)
            | exact resolve b5e17 b5e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e184
          have b5e389 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e383 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e383
          have b5e1755 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e69 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e69
          have b5e1756 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1755
               have r₂ := b5e24
               grind)
            | exact resolve b5e1755 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1755
          have b5e1757 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1756
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1756
            | exact resolve b5e1756 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1756
          have b5e1758 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1757
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e1757
            | exact resolve b5e1757 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e1757
          have b5e1773 : y = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e183 (σ x) (σ y)
               have i₂ := b5e1758
               grind)
            | exact superpose b5e1758 b5e183
            | exact resolve b5e183 b5e1758
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e183 b5e1758
          have b5e2214 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1773
               grind)
            | exact superpose b5e1773 b5e23
            | exact resolve b5e23 b5e1773
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1773
          have b5e4006 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e389
          have b5e4063 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e4006 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4006
          have b5e4111 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e4063 (τ X0)
               grind)
            | exact superpose b5e4063 b5e27
            | exact resolve b5e27 b5e4063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e4063
          have b5e4112 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e4111 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e4111
            | exact resolve b5e4111 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4111
          have b5e4128 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e284 X0 (σ y)
               have i₂ := b5e4112 (M.op X0 X0)
               grind)
            | exact superpose b5e4112 b5e284
            | (have j0 := b5e284 x (M.op X0 X0)
               grind)
            | exact resolve b5e284 b5e4112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e284 b5e4112
          have b5e4136 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have j0 := b5e4128 X0
               grind)
            | (have r₁ := b5e4128 X0
               have r₂ := b5e2214
               grind)
            | exact resolve b5e4128 b5e2214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2214 b5e4128
          have b5e4329 : y ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e4136 x
               grind)
            | exact superpose b5e4136 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e4136 x
               grind)
            | exact resolve b5e21 b5e4136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4136
          have b5e4330 : False := by grind
          exact b5e4330
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
        have b6e40 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e12 X2 X1 x
             grind)
          | (have i₁ := b6e12 X0 X1 (M.op (M.op X1 X1) X1)
             have i₂ := b6e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1
          grind
        have b6e61 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X1
             have i₂ := b6e40 X0
             grind)
          | exact superpose b6e40 b6e40
          | exact resolve b6e40 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e83 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e94 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e20
             grind)
          | exact resolve b6e83 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e99 : x = (M.op x y) := by
          first
          | (have r₁ := b6e94
             have r₂ := b6e21
             grind)
          | exact resolve b6e94 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e94
        have b6e102 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e99
             grind)
          | exact superpose b6e99 b6e21
          | exact resolve b6e21 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e236 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e47 X0 y x
             have i₂ := b6e99
             grind)
          | exact superpose b6e99 b6e47
          | exact resolve b6e47 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47 b6e99
        have b6e1447 : ∀ X0 : G, (M.op x x) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e61 (M.op (σ y) y) X0
             have i₂ := b6e236 (σ y)
             grind)
          | exact superpose b6e236 b6e61
          | exact resolve b6e61 b6e236
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e236
        have b6e1931 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b6e49 (σ y) X0
             have i₂ := b6e1447 (M.op (σ y) X0)
             grind)
          | exact superpose b6e1447 b6e49
          | exact resolve b6e49 b6e1447
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e1447
        have b6e3247 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e81 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e81
          | exact resolve b6e81 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e3390 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3247
        have b6e6114 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3390
             grind)
          | exact superpose b6e3390 b6e13
          | exact resolve b6e13 b6e3390
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e6131 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e6114
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e6114
          | exact resolve b6e6114 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6114
        have b6e6242 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e6131
             grind)
          | exact superpose b6e6131 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e6131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6131
        have b6e6243 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e6242
        have b6e6245 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e6243
             have r₂ := b6e20
             grind)
          | exact resolve b6e6243 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6243
        have b6e6341 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1931 x
             have i₂ := b6e6245
             grind)
          | exact superpose b6e6245 b6e1931
          | exact resolve b6e1931 b6e6245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1931 b6e6245
        have b6e8405 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3390
             have i₂ := b6e6341
             grind)
          | exact superpose b6e6341 b6e3390
          | exact resolve b6e3390 b6e6341
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3390 b6e6341
        have b6e8414 : (σ x) = (σ y) := by grind
        clear b6e8405
        have b6e8705 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e8414
             grind)
          | exact superpose b6e8414 b6e13
          | exact resolve b6e13 b6e8414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8414
        have b6e8721 : x = y := by
          first
          | (have i₁ := b6e8705
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e8705
          | exact resolve b6e8705 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8705
        have b6e8742 : False := by grind
        exact b6e8742
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X1 x
               have i₂ := b7e13 X2 X1 x
               grind)
            | (have i₁ := b7e13 X0 X1 (M.op (M.op X1 X1) X1)
               have i₂ := b7e13 (M.op X1 X1) X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b7e38 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b7e29 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e29
            | exact resolve b7e29 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e48 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e45
          have b7e49 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e48
               have r₂ := b7e23
               grind)
            | exact resolve b7e48 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e49
            | exact resolve b7e49 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e53 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : x = (k x y) := by
            first
            | (have i₁ := b7e53
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e53
            | exact resolve b7e53 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e72 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e54
               grind)
            | exact superpose b7e54 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e73 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e75 : x = (M.op x y) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e22
               grind)
            | exact resolve b7e73 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e99 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op (σ y) (σ y)) X0 X1
               have i₂ := b7e38 (M.op (M.op (σ y) (σ y)) X0)
               grind)
            | exact superpose b7e38 b7e13
            | exact resolve b7e13 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e197 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e35 X0 y x
               have i₂ := b7e75
               grind)
            | exact superpose b7e75 b7e35
            | exact resolve b7e35 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e214 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op (M.op (M.op X2 X1) (M.op X2 X1)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X2 X1) X3
               have i₂ := b7e35 X2 X1 X0
               grind)
            | (have i₁ := b7e13 X2 (M.op X2 X1) X3
               have i₂ := b7e35 X0 X1 X2
               grind)
            | exact superpose b7e35 b7e13
            | exact resolve b7e13 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e218 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b7e38 (M.op (M.op (σ y) (σ y)) X1)
               have i₂ := b7e35 (M.op (σ y) (σ y)) X1 X0
               grind)
            | (have i₁ := b7e38 (M.op (M.op (σ y) (σ y)) X1)
               have i₂ := b7e35 X0 X1 (M.op (σ y) (σ y))
               grind)
            | exact superpose b7e35 b7e38
            | exact resolve b7e38 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e220 : ∀ X0 X1 X2 : G, (σ y) = (M.op X2 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e214 X0 X1 X2 x
               have i₂ := b7e99 (M.op X2 X1) x
               grind)
            | exact superpose b7e99 b7e214
            | exact resolve b7e214 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99 b7e214
          have b7e226 : (σ y) = (M.op x x) := by
            first
            | (have i₁ := b7e197 x
               have i₂ := b7e218 x y
               grind)
            | exact superpose b7e218 b7e197
            | exact resolve b7e197 b7e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e197
          have b7e239 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) := by
            intro X2
            first
            | (have i₁ := b7e220 x x X2
               have i₂ := b7e218 x x
               grind)
            | exact superpose b7e218 b7e220
            | exact resolve b7e220 b7e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e220
          have b7e247 : y ≠ (σ y) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e226
               grind)
            | exact superpose b7e226 b7e21
            | exact resolve b7e21 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e395 : (σ y) = (k (σ y) (M.op x (σ y))) := by
            first
            | (have i₁ := b7e37 x x
               have i₂ := b7e226
               grind)
            | exact superpose b7e226 b7e37
            | exact resolve b7e37 b7e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37 b7e226
          have b7e413 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e395
               have i₂ := b7e239 x
               grind)
            | exact superpose b7e239 b7e395
            | exact resolve b7e395 b7e239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e239 b7e395
          have b7e432 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e413
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e413
            | exact resolve b7e413 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e413
          have b7e1445 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e432
               grind)
            | exact superpose b7e432 b7e14
            | exact resolve b7e14 b7e432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e432
          have b7e1447 : y = (k y y) := by
            first
            | (have i₁ := b7e1445
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1445
            | exact resolve b7e1445 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1445
          have b7e1751 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1447
               grind)
            | exact superpose b7e1447 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1447
          have b7e1752 : y = (M.op y y) := by grind
          clear b7e1751
          have b7e1773 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e35 X0 y y
               have i₂ := b7e1752
               grind)
            | exact superpose b7e1752 b7e35
            | exact resolve b7e35 b7e1752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e1775 : (σ y) = (M.op y y) := by
            first
            | (have i₁ := b7e1773 x
               have i₂ := b7e218 x y
               grind)
            | exact superpose b7e218 b7e1773
            | exact resolve b7e1773 b7e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e218 b7e1773
          have b7e1786 : y = (σ y) := by
            first
            | (have i₁ := b7e1775
               have i₂ := b7e1752
               grind)
            | exact superpose b7e1752 b7e1775
            | exact resolve b7e1775 b7e1752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1752 b7e1775
          have b7e1794 : False := by grind
          exact b7e1794
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b8e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e1478 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e1479 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1478
               have r₂ := b8e24
               grind)
            | exact resolve b8e1478 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1478
          have b8e1480 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1479
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1479
            | exact resolve b8e1479 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1479
          have b8e1483 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1480
               grind)
            | exact superpose b8e1480 b8e20
            | exact resolve b8e20 b8e1480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1480
          have b8e1891 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1483
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1483
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1483 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1483
          have b8e1892 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1891
          have b8e1895 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1892
               have r₂ := b8e21
               grind)
            | exact resolve b8e1892 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1892
          have b8e1898 : False := by grind
          exact b8e1898

/-- `Equation4444`: `x ◇ (y ◇ x) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4444 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4444 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4444.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e44 X0 x
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e44
        | exact resolve b0e44 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e46 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e45 X0
           have i₂ := b0e38 (M.op x y)
           grind)
        | exact superpose b0e38 b0e45
        | exact resolve b0e45 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e45
      have b0e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
      have b0e71 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
      have b0e74 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op x y)
           have i₂ := b0e46 (M.op X1 X0)
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e103 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op x y) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e74 X0 X1
           grind)
        | exact superpose b0e74 b0e11
        | exact resolve b0e11 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e117 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e412 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e117 (M.op x y)
           have i₂ := b0e46 (σ y)
           grind)
        | exact superpose b0e46 b0e117
        | exact resolve b0e117 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e117
      have b0e1921 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e59 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59
      have b0e1922 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e1921 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1921
      have b0e3158 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e1922 (M.op x y)
           have i₂ := b0e71
           grind)
        | exact superpose b0e71 b0e1922
        | (have j0 := b0e1922 (M.op x y)
           grind)
        | exact resolve b0e1922 b0e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71 b0e1922
      have b0e3168 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e3158
      have b0e5365 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ (M.op x y)) (σ (M.op x y)) x
           have i₂ := b0e3168
           grind)
        | exact superpose b0e3168 b0e11
        | exact resolve b0e11 b0e3168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e5377 : ∀ X0 : G, (M.op x y) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e103 (σ (M.op x y)) (σ (M.op x y)) X0
           have i₂ := b0e3168
           grind)
        | exact superpose b0e3168 b0e103
        | exact resolve b0e103 b0e3168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103
      have b0e5390 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e5365 X0
           have i₂ := b0e3168
           grind)
        | exact superpose b0e3168 b0e5365
        | exact resolve b0e5365 b0e3168
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3168 b0e5365
      have b0e5404 : (M.op x y) = (σ (M.op x y)) := by
        first
        | (have i₁ := b0e5390 x
           have i₂ := b0e5377 x
           grind)
        | exact superpose b0e5377 b0e5390
        | exact resolve b0e5390 b0e5377
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5377 b0e5390
      have b0e5417 : False := by grind
      exact b0e5417
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e135 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e31 (σ x)
             grind)
          | exact superpose b1e31 b1e22
          | exact resolve b1e22 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e164 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e31 X0
             have i₂ := b1e135
             grind)
          | exact superpose b1e135 b1e31
          | exact resolve b1e31 b1e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e166 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e135
             grind)
          | exact superpose b1e135 b1e19
          | exact resolve b1e19 b1e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e135
        have b1e482 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b1e164
        have b1e502 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e482
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e482
          | exact resolve b1e482 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e482
        have b1e855 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e502
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e502
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e502 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e502
        have b1e859 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e855
        have b1e863 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e859
             have i₂ := b1e32 y
             grind)
          | exact superpose b1e32 b1e859
          | exact resolve b1e859 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e859
        have b1e865 : y = (M.op y y) := by
          first
          | (have r₁ := b1e863
             have r₂ := b1e166
             grind)
          | exact resolve b1e863 b1e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e863
        have b1e866 : y = (M.op x y) := by
          first
          | (have i₁ := b1e865
             have i₂ := b1e32 y
             grind)
          | exact superpose b1e32 b1e865
          | exact resolve b1e865 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e865
        have b1e1137 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e166
             have i₂ := b1e866
             grind)
          | exact superpose b1e866 b1e166
          | exact resolve b1e166 b1e866
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e166 b1e866
        have b1e1149 : False := by grind
        exact b1e1149
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
        have b2e29 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e37 X0 x
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e37
          | exact resolve b2e37 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e39 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e38 X0
             have i₂ := b2e29 (M.op x y)
             grind)
          | exact superpose b2e29 b2e38
          | exact resolve b2e38 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e38
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x y) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op x y)
             have i₂ := b2e39 (M.op X1 X0)
             grind)
          | exact superpose b2e39 b2e12
          | exact resolve b2e12 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e90 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op x y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e64 X0 X1
             grind)
          | exact superpose b2e64 b2e12
          | exact resolve b2e12 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e392 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e105
        have b2e405 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e392 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e392
          | exact resolve b2e392 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e392
        have b2e946 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e947 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e946
             have r₂ := b2e22
             grind)
          | exact resolve b2e946 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e946
        have b2e948 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e947
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e947
          | exact resolve b2e947 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e947
        have b2e949 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e948
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e948
          | exact resolve b2e948 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e948
        have b2e963 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e90 (σ y) (σ x) X0
             have i₂ := b2e949
             grind)
          | exact superpose b2e949 b2e90
          | exact resolve b2e90 b2e949
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e1170 : (M.op x y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e963 (σ x)
             grind)
          | exact superpose b2e963 b2e21
          | exact resolve b2e21 b2e963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1171 : (M.op x y) = (σ x) := by
          first
          | (have i₁ := b2e949
             have i₂ := b2e963 (σ y)
             grind)
          | exact superpose b2e963 b2e949
          | exact resolve b2e949 b2e963
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e949 b2e963
        have b2e1204 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e1170
             have i₂ := b2e1171
             grind)
          | exact superpose b2e1171 b2e1170
          | exact resolve b2e1170 b2e1171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1170
        have b2e1910 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e39 X0
             have i₂ := b2e1171
             grind)
          | exact superpose b2e1171 b2e39
          | exact resolve b2e39 b2e1171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e1171
        have b2e2148 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e405 x
             have i₂ := b2e1910 (σ x)
             grind)
          | exact superpose b2e1910 b2e405
          | exact resolve b2e405 b2e1910
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e405 b2e1910
        have b2e2155 : x = (k x x) := by
          first
          | (have i₁ := b2e2148
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e2148
          | exact resolve b2e2148 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2148
        have b2e2355 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e2155
             grind)
          | exact superpose b2e2155 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e2155
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2155
        have b2e2356 : x = (M.op x x) := by grind
        clear b2e2355
        have b2e2372 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e2356
             grind)
          | exact superpose b2e2356 b2e20
          | exact resolve b2e20 b2e2356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2356
        have b2e2464 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1204
             have i₂ := b2e2372
             grind)
          | exact superpose b2e2372 b2e1204
          | exact resolve b2e1204 b2e2372
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1204 b2e2372
        have b2e2466 : False := by grind
        exact b2e2466
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X0 X3
             have i₂ := b3e12 X1 X0 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ x) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e45 X0
             grind)
          | exact superpose b3e45 b3e12
          | exact resolve b3e12 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e53 : y = (M.op x y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e45 x
             grind)
          | exact superpose b3e45 b3e21
          | exact resolve b3e21 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e52 X0 x
             have i₂ := b3e12 y x x
             grind)
          | exact superpose b3e12 b3e52
          | exact resolve b3e52 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e56 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b3e54 X0
             have i₂ := b3e45 (M.op x y)
             grind)
          | exact superpose b3e45 b3e54
          | exact resolve b3e54 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e57 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e56 X0
             have i₂ := b3e53
             grind)
          | exact superpose b3e53 b3e56
          | exact resolve b3e56 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e62 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e45 X0
             grind)
          | exact superpose b3e45 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | exact resolve b3e16 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e64 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e62 X0
             grind)
          | (have r₁ := b3e62 X0
             have r₂ := b3e53
             grind)
          | exact resolve b3e62 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e62
        have b3e83 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) ∨ (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 (M.op X2 X1)) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 X1)
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X1 X0) X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 (M.op X2 X1) X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e104 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e57 (M.op X1 X0)
             grind)
          | exact superpose b3e57 b3e12
          | exact resolve b3e12 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e111 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e19
             have i₂ := b3e44 X0
             grind)
          | exact superpose b3e44 b3e19
          | exact resolve b3e19 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e122 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e111 X0
             have i₂ := b3e57 x
             grind)
          | exact superpose b3e57 b3e111
          | exact resolve b3e111 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111
        have b3e127 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e122 y
             have i₂ := b3e57 (σ y)
             grind)
          | exact superpose b3e57 b3e122
          | exact resolve b3e122 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e166 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e57 (M.op X0 X1)
             have i₂ := b3e40 X0 X1 y X2
             grind)
          | (have i₁ := b3e57 (M.op X0 X1)
             have i₂ := b3e40 X0 X1 X2 y
             grind)
          | exact superpose b3e40 b3e57
          | exact resolve b3e57 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e57
        have b3e2322 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e64
        have b3e2364 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e2322 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2322
        have b3e2422 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e28 X0 y
             have i₂ := b3e2364 (τ X0)
             grind)
          | exact superpose b3e2364 b3e28
          | exact resolve b3e28 b3e2364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28 b3e2364
        have b3e2423 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2422 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e2422
          | exact resolve b3e2422 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2422
        have b3e2457 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op X1 (M.op X0 X1)) ∨ (σ y) = (M.op (σ y) (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e83 (σ y) X1 X0
             have i₂ := b3e2423 (M.op X0 X1)
             grind)
          | exact superpose b3e2423 b3e83
          | (have j0 := b3e83 (σ y) X1 X0
             grind)
          | exact resolve b3e83 b3e2423
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83 b3e2423
        have b3e2463 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have j0 := b3e2457 X0 X1
             grind)
          | (have r₁ := b3e2457 X0 (σ y)
             have r₂ := b3e122 (M.op X0 (σ y))
             grind)
          | (have r₁ := b3e2457 X0 X1
             have r₂ := b3e122 (M.op X0 X1)
             grind)
          | exact resolve b3e2457 b3e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e122 b3e2457
        have b3e2475 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (σ y) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e2463 X0 X1
             have i₂ := b3e166 X0 X1 (σ y)
             grind)
          | exact superpose b3e166 b3e2463
          | (have j0 := b3e2463 X0 X1
             grind)
          | exact resolve b3e2463 b3e166
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e166 b3e2463
        have b3e2479 : ∀ X0 X1 : G, y = (σ y) ∨ (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e2475 X0 X1
             have i₂ := b3e104 X1 X0
             grind)
          | exact superpose b3e104 b3e2475
          | (have j0 := b3e2475 X0 X1
             grind)
          | exact resolve b3e2475 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104 b3e2475
        have b3e2481 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have j0 := b3e2479 X0 X1
             grind)
          | (have r₁ := b3e2479 X0 X1
             have r₂ := b3e127
             grind)
          | exact resolve b3e2479 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127 b3e2479
        have b3e2713 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e2481 x x
             grind)
          | exact superpose b3e2481 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e2481 x x
             grind)
          | exact resolve b3e20 b3e2481
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2481
        have b3e2714 : False := by grind
        exact b3e2714
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e33 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : y = (M.op x y) := by
            first
            | (have i₁ := b4e22
               have i₂ := b4e33 x
               grind)
            | exact superpose b4e33 b4e22
            | exact resolve b4e22 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e40 X0 x
               have i₂ := b4e13 y x x
               grind)
            | exact superpose b4e13 b4e40
            | exact resolve b4e40 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e44 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e33 (M.op x y)
               grind)
            | exact superpose b4e33 b4e42
            | exact resolve b4e42 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e42
          have b4e45 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e44 X0
               have i₂ := b4e41
               grind)
            | exact superpose b4e41 b4e44
            | exact resolve b4e44 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e44
          have b4e108 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e20
            | exact resolve b4e20 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e124 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e108 X0
               have i₂ := b4e45 x
               grind)
            | exact superpose b4e45 b4e108
            | exact resolve b4e108 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e108
          have b4e131 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e124 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e124
            | (have r₁ := b4e124 (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e124 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e136 : False := by grind
          exact b4e136
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X0 X3
               have i₂ := b5e13 X1 X0 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e30 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : y = (M.op x y) := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e22
            | exact resolve b5e22 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e39 X0 x
               have i₂ := b5e13 y x x
               grind)
            | exact superpose b5e13 b5e39
            | exact resolve b5e39 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e43 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e41 X0
               have i₂ := b5e30 (M.op x y)
               grind)
            | exact superpose b5e30 b5e41
            | exact resolve b5e41 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e44 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e43 X0
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e43
            | exact resolve b5e43 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e46 : ∀ X0 : G, y ≠ (M.op x y) ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | exact resolve b5e17 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e46 X0
               grind)
            | (have r₁ := b5e46 X0
               have r₂ := b5e40
               grind)
            | exact resolve b5e46 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e46
          have b5e61 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X0 X2
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e86 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e133 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e44 (M.op X0 X1)
               have i₂ := b5e28 X0 X1 y X2
               grind)
            | (have i₁ := b5e44 (M.op X0 X1)
               have i₂ := b5e28 X0 X1 X2 y
               grind)
            | exact superpose b5e28 b5e44
            | exact resolve b5e44 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e44
          have b5e370 : ∀ X0 X1 X2 : G, y = (M.op X0 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e133 X1 X1 X2
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e133 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e133
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e133 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e756 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e51
          have b5e778 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e756 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e756
          have b5e873 : ∀ X0 : G, y ≠ (M.op x X0) ∨ (M.op x x) = (k x x) ∨ x = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e61 x x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e61 x x x
               grind)
            | exact superpose b5e61 b5e21
            | (have j1 := b5e61 x x x
               grind)
            | exact resolve b5e21 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e925 : (M.op x x) = (k x x) ∨ x = (M.op x x) := by
            first
            | (have j1 := b5e370 x x x
               grind)
            | (have r₁ := b5e873 x
               have r₂ := b5e370 x x x
               grind)
            | exact resolve b5e873 b5e370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e370 b5e873
          have b5e983 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e984 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e983
               have r₂ := b5e24
               grind)
            | exact resolve b5e983 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e983
          have b5e985 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e984
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e984
            | exact resolve b5e984 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e984
          have b5e986 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e985
               have i₂ := b5e778 x
               grind)
            | exact superpose b5e778 b5e985
            | exact resolve b5e985 b5e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e985
          have b5e1219 : ∀ X0 : G, y = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e133 (σ x) (σ y) X0
               have i₂ := b5e986
               grind)
            | exact superpose b5e986 b5e133
            | exact resolve b5e133 b5e986
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1744 : y = (σ x) := by
            first
            | (have i₁ := b5e986
               have i₂ := b5e1219 (σ y)
               grind)
            | exact superpose b5e1219 b5e986
            | exact resolve b5e986 b5e1219
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e986 b5e1219
          have b5e1872 : x = (τ y) := by
            first
            | (have i₁ := b5e14 x
               have i₂ := b5e1744
               grind)
            | exact superpose b5e1744 b5e14
            | exact resolve b5e14 b5e1744
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1744
          have b5e1957 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ y)) := by
            intro X0
            first
            | (have i₁ := b5e86 X0 y
               have i₂ := b5e778 (σ X0)
               grind)
            | exact superpose b5e778 b5e86
            | exact resolve b5e86 b5e778
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86 b5e778
          have b5e1967 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b5e1957 X0
               have i₂ := b5e1872
               grind)
            | exact superpose b5e1872 b5e1957
            | exact resolve b5e1957 b5e1872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1872 b5e1957
          have b5e1974 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1967 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1967
            | exact resolve b5e1967 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1967
          have b5e2030 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1974 x
               have i₂ := b5e925
               grind)
            | exact superpose b5e925 b5e1974
            | exact resolve b5e1974 b5e925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e925 b5e1974
          have b5e2031 : x = (M.op x x) := by grind
          clear b5e2030
          have b5e2047 : ∀ X0 : G, y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e133 x x X0
               have i₂ := b5e2031
               grind)
            | exact superpose b5e2031 b5e133
            | exact resolve b5e133 b5e2031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e133 b5e2031
          have b5e2197 : y ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e2047 x
               grind)
            | exact superpose b5e2047 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e2047 x
               grind)
            | exact resolve b5e21 b5e2047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2047
          have b5e2198 : False := by grind
          exact b5e2198
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
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
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X0 X3
             have i₂ := b6e12 X1 X0 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e83 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e92 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e83
             have r₂ := b6e20
             grind)
          | exact resolve b6e83 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e95 : x = (M.op x y) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e21
             grind)
          | exact resolve b6e92 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e98 : ∀ X0 : G, (M.op y x) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e12 y x x
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e12
          | exact resolve b6e12 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e113 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 x y x x
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e40
          | exact resolve b6e40 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e196 : ∀ X0 : G, y ≠ (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e21
             have i₂ := b6e98 X0
             grind)
          | exact superpose b6e98 b6e21
          | exact resolve b6e21 b6e98
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98
        have b6e242 : x ≠ y := by
          first
          | (have i₁ := b6e196 y
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e196
          | exact resolve b6e196 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e196
        have b6e452 : ∀ X0 : G, x = (k x (M.op x X0)) := by
          intro X0
          grind
        have b6e466 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e95
             have i₂ := b6e113 y X0
             grind)
          | (have i₁ := b6e95
             have i₂ := b6e113 X0 y
             grind)
          | exact superpose b6e113 b6e95
          | exact resolve b6e95 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95 b6e113
        have b6e476 : x = (k x x) := by
          first
          | (have i₁ := b6e452 x
             have i₂ := b6e466 x
             grind)
          | exact superpose b6e466 b6e452
          | exact resolve b6e452 b6e466
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e452 b6e466
        have b6e1528 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e81 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e81
          | exact resolve b6e81 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e1607 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b6e1528
        have b6e1637 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1607
             have i₂ := b6e476
             grind)
          | exact superpose b6e476 b6e1607
          | exact resolve b6e1607 b6e476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e476 b6e1607
        have b6e1638 : (σ x) = (σ y) := by grind
        clear b6e1637
        have b6e1700 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1638
             grind)
          | exact superpose b6e1638 b6e13
          | exact resolve b6e13 b6e1638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1638
        have b6e1713 : x = y := by
          first
          | (have i₁ := b6e1700
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1700
          | exact resolve b6e1700 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1700
        have b6e1719 : False := by grind
        exact b6e1719
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 (M.op X1 X0) X2
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X3) = (M.op X2 (M.op X1 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X1 (M.op X0 (M.op X1 X2))
               have i₂ := b7e13 (M.op X1 X2) X0 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e32 X0 X1 X2 x
               have i₂ := b7e33 X0 X1 X0 x
               grind)
            | exact superpose b7e33 b7e32
            | exact resolve b7e32 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e33
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
          have b7e48 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e46
               have r₂ := b7e23
               grind)
            | exact resolve b7e46 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e49 : (σ x) = (σ (k x y)) := by
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
          have b7e61 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
          have b7e67 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e68 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e91 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e20
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e20
            | exact resolve b7e20 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e95 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by grind
          have b7e99 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 (σ x)
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e103 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e99
               grind)
            | exact superpose b7e99 b7e95
            | exact resolve b7e95 b7e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95 b7e99
          have b7e107 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e91 X0
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e91
            | exact resolve b7e91 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e91
          have b7e110 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e103
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e103
            | exact resolve b7e103 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e150 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e107 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e107
            | exact resolve b7e107 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e250 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e14
            | exact resolve b7e14 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e252 : y = (k y y) := by
            first
            | (have i₁ := b7e250
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e250
            | exact resolve b7e250 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e250
          have b7e326 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e252
               grind)
            | exact superpose b7e252 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e252
          have b7e327 : y = (M.op y y) := by grind
          clear b7e326
          have b7e481 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e35 y y x
               have i₂ := b7e327
               grind)
            | exact superpose b7e327 b7e35
            | exact resolve b7e35 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e484 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e481 X0
               have i₂ := b7e327
               grind)
            | exact superpose b7e327 b7e481
            | exact resolve b7e481 b7e327
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e327 b7e481
          have b7e848 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e484 x
               grind)
            | exact superpose b7e484 b7e68
            | exact resolve b7e68 b7e484
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e484
          have b7e872 : False := by grind
          exact b7e872
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e867 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e868 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e867
               have r₂ := b8e24
               grind)
            | exact resolve b8e867 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e867
          have b8e869 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e868
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e868
            | exact resolve b8e868 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e868
          have b8e872 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e869
               grind)
            | exact superpose b8e869 b8e20
            | exact resolve b8e20 b8e869
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e869
          have b8e932 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e872
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e872
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e872 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e872
          have b8e933 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e932
          have b8e936 : y = (M.op y x) := by
            first
            | (have r₁ := b8e933
               have r₂ := b8e21
               grind)
            | exact resolve b8e933 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e933
          have b8e939 : False := by grind
          exact b8e939

/-- `Equation4476`: `x ◇ (y ◇ y) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxx_x_pyx_Equation4476 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4476 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4476.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op X2 (M.op (M.op (M.op X0 X0) X1) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 (M.op X0 X0) X3
           have i₂ := b0e11 (M.op X0 X0) X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X2 X3
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X3 (M.op X2 X2)
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X0 X2) X3 X1
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e11 y X0 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X0)) = (M.op X2 (M.op X0 (M.op X0 X0))) := by
        intro X0 X2 X3
        first
        | (have i₁ := b0e27 X0 x X2 X3
           have i₂ := b0e30 X0 X0 x X0
           grind)
        | exact superpose b0e30 b0e27
        | exact resolve b0e27 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e36 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op (M.op (M.op X0 X0) X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 (M.op X0 X0)
           have i₂ := b0e11 (M.op X0 X0) X0 X1
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op y (M.op X1 X1)) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X1 (M.op X0 X0)
           have i₂ := b0e33 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e39 X0 X1
           have i₂ := b0e33 X1
           grind)
        | exact superpose b0e33 b0e39
        | exact resolve b0e39 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e39
      have b0e41 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op X0 (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e36 X0 x
           have i₂ := b0e30 X0 X0 x X0
           grind)
        | exact superpose b0e30 b0e36
        | exact resolve b0e36 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e36
      have b0e72 : ∀ X0 X1 X2 : G, (M.op (M.op y X1) (M.op X2 X2)) = (M.op (M.op x X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op y X1) X2 X0
           have i₂ := b0e38 X0 X1
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73 : ∀ X1 X2 : G, (M.op x X2) = (M.op (M.op y X1) (M.op X2 X2)) := by
        intro X1 X2
        first
        | (have i₁ := b0e72 x X1 X2
           have i₂ := b0e40 x X2
           grind)
        | exact superpose b0e40 b0e72
        | exact resolve b0e72 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e72
      have b0e77 : ∀ X2 : G, (M.op x X2) = (M.op x (M.op X2 X2)) := by
        intro X2
        first
        | (have i₁ := b0e73 x X2
           have i₂ := b0e38 (M.op X2 X2) x
           grind)
        | exact superpose b0e38 b0e73
        | exact resolve b0e73 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e73
      have b0e80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e151 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (σ y) X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e28
        | exact resolve b0e28 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e370 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X0)) = (M.op (M.op (σ y) (M.op X1 X1)) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e31 (σ y) X1 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e31
        | exact resolve b0e31 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e501 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e370 X0 x
           have i₂ := b0e151 (M.op x x) X0
           grind)
        | exact superpose b0e151 b0e370
        | exact resolve b0e370 b0e151
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e370
      have b0e2482 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) (σ X1)
           have i₂ := b0e80 X0 X1
           grind)
        | exact superpose b0e80 b0e14
        | (have j0 := b0e14 (σ X0) (σ X1)
           have j1 := b0e80 X0 X1
           grind)
        | (have r₁ := b0e14 (σ X0) (σ X1)
           have r₂ := b0e80 X0 X1
           grind)
        | (have r₁ := b0e14 (σ X1) (σ X0)
           have r₂ := b0e80 X0 X1
           grind)
        | exact resolve b0e14 b0e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e2497 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e2482 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2482
      have b0e2521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2497 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e2497
        | (have j0 := b0e2497 X0 X1
           grind)
        | exact resolve b0e2497 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2497
      have b0e113060 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e2521 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2521
      have b0e113062 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e113060 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113060
      have b0e232633 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e113062 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e113062
        | exact resolve b0e113062 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e113062
      have b0e233037 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e232633 X0
           have i₂ := b0e22 X0 (τ X0)
           grind)
        | exact superpose b0e22 b0e232633
        | (have j0 := b0e232633 X0
           grind)
        | exact resolve b0e232633 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e232633
      have b0e233067 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e233037 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e233037
        | (have j0 := b0e233037 X0
           grind)
        | exact resolve b0e233037 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233037
      have b0e233075 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e233067 X0
           have j1 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e233067 X0
           have r₂ := b0e14 X0 X0
           grind)
        | exact resolve b0e233067 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233067
      have b0e233149 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e233075 (σ X0)
           grind)
        | exact superpose b0e233075 b0e17
        | exact resolve b0e17 b0e233075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e233191 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e233149 X0
           have i₂ := b0e233075 X0
           grind)
        | exact superpose b0e233075 b0e233149
        | exact resolve b0e233149 b0e233075
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233075 b0e233149
      have b0e239444 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ (M.op y y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e151 (σ y) X0
           have i₂ := b0e233191 y
           grind)
        | exact superpose b0e233191 b0e151
        | exact resolve b0e151 b0e233191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151
      have b0e239520 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ x) (σ (M.op X0 X0))) := by
        intro X0
        first
        | (have i₁ := b0e501 (σ X0)
           have i₂ := b0e233191 X0
           grind)
        | exact superpose b0e233191 b0e501
        | exact resolve b0e501 b0e233191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e501
      have b0e250025 : (M.op (σ x) (σ (M.op y y))) = (σ (M.op (M.op y y) (M.op y y))) := by
        first
        | (have i₁ := b0e233191 (M.op y y)
           have i₂ := b0e239444 (σ (M.op y y))
           grind)
        | exact superpose b0e239444 b0e233191
        | exact resolve b0e233191 b0e239444
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233191 b0e239444
      have b0e250604 : (M.op (σ x) (σ (M.op y y))) = (σ (M.op y (M.op y (M.op y y)))) := by
        first
        | (have i₁ := b0e250025
           have i₂ := b0e35 y y y
           grind)
        | exact superpose b0e35 b0e250025
        | exact resolve b0e250025 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e250025
      have b0e250876 : (M.op (σ x) (σ (M.op y y))) = (σ (M.op x (M.op y y))) := by
        first
        | (have i₁ := b0e250604
           have i₂ := b0e41 y
           grind)
        | exact superpose b0e41 b0e250604
        | exact resolve b0e250604 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e250604
      have b0e251069 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y y))) := by
        first
        | (have i₁ := b0e250876
           have i₂ := b0e77 y
           grind)
        | (have i₁ := b0e250876
           have i₂ := b0e77 (M.op y y)
           grind)
        | exact superpose b0e77 b0e250876
        | exact resolve b0e250876 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77 b0e250876
      have b0e251171 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e251069
           have i₂ := b0e239520 y
           grind)
        | exact superpose b0e239520 b0e251069
        | exact resolve b0e251069 b0e239520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e239520 b0e251069
      have b0e251229 : False := by grind
      exact b0e251229
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
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
        have b1e37 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 X1
             have i₂ := b1e32 X0
             grind)
          | exact superpose b1e32 b1e12
          | exact resolve b1e12 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e43 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | (have r₁ := b1e15 (σ y) (σ x)
             have r₂ := b1e22
             grind)
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear b1e43
        have b1e49 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e54 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) := by
          first
          | (have i₁ := b1e16 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16
          | (have j0 := b1e16 y x
             grind)
          | (have r₁ := b1e16 y x
             have r₂ := b1e20
             grind)
          | exact resolve b1e16 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : y = (k y x) ∨ y = (M.op x y) := by grind
        clear b1e54
        have b1e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e114 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e15
          | exact resolve b1e15 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e116 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e114
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e114
          | exact resolve b1e114 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e114
        have b1e2342 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e70 y y
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e70
          | exact resolve b1e70 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49 b1e70
        have b1e2409 : (σ y) = (σ (k y x)) ∨ (σ (k y x)) = (σ (k y y)) := by grind
        clear b1e2342
        have b1e2421 : (σ (k y x)) = (σ (k y y)) := by
          first
          | (have r₁ := b1e2409
             have r₂ := b1e116
             grind)
          | exact resolve b1e2409 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e2409
        have b1e2438 : (k y y) = (τ (σ (k y x))) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e2421
             grind)
          | exact superpose b1e2421 b1e13
          | exact resolve b1e13 b1e2421
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2421
        have b1e2456 : (k y x) = (k y y) := by
          first
          | (have i₁ := b1e2438
             have i₂ := b1e13 (k y x)
             grind)
          | exact superpose b1e13 b1e2438
          | exact resolve b1e2438 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2438
        have b1e2494 : (k y x) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e17 y y
             have i₂ := b1e2456
             grind)
          | exact superpose b1e2456 b1e17
          | (have j0 := b1e17 y y
             grind)
          | exact resolve b1e17 b1e2456
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2456
        have b1e2495 : (k y x) = (M.op y y) ∨ y = (M.op y y) := by grind
        clear b1e2494
        have b1e9272 : y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e2495
             grind)
          | exact superpose b1e2495 b1e56
          | exact resolve b1e56 b1e2495
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e2495
        have b1e9288 : y = (M.op y y) ∨ y = (M.op x y) := by grind
        clear b1e9272
        have b1e10097 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ y = (M.op x y) := by
          intro X0
          first
          | (have i₁ := b1e37 X0 y
             have i₂ := b1e9288
             grind)
          | exact superpose b1e9288 b1e37
          | exact resolve b1e37 b1e9288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e11924 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b1e9288
             have i₂ := b1e10097 y
             grind)
          | exact superpose b1e10097 b1e9288
          | exact resolve b1e9288 b1e10097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9288 b1e10097
        have b1e11994 : y = (M.op x y) := by grind
        clear b1e11924
        have b1e12237 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e11994
             grind)
          | exact superpose b1e11994 b1e23
          | exact resolve b1e23 b1e11994
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e11994
        have b1e12272 : False := by grind
        exact b1e12272
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x X0) := by
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
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X3 (M.op X2 X2)
             have i₂ := b2e12 X0 X2 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 X1
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 : G, (M.op y (M.op X1 X1)) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X1 (M.op X0 X0)
             have i₂ := b2e28 X0
             grind)
          | exact superpose b2e28 b2e12
          | exact resolve b2e12 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e36 X0 X1
             have i₂ := b2e28 X1
             grind)
          | exact superpose b2e28 b2e36
          | exact resolve b2e36 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e46 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : y = (k y x) ∨ y = (M.op x y) := by grind
        clear b2e46
        have b2e62 : ∀ X0 X1 X2 : G, (M.op (M.op y X1) (M.op X2 X2)) = (M.op (M.op x X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 (M.op y X1) X2 X0
             have i₂ := b2e35 X0 X1
             grind)
          | exact superpose b2e35 b2e12
          | exact resolve b2e12 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e63 : ∀ X1 X2 : G, (M.op x X2) = (M.op (M.op y X1) (M.op X2 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b2e62 x X1 X2
             have i₂ := b2e37 x X2
             grind)
          | exact superpose b2e37 b2e62
          | exact resolve b2e62 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e67 : ∀ X2 : G, (M.op x X2) = (M.op x (M.op X2 X2)) := by
          intro X2
          first
          | (have i₁ := b2e63 x X2
             have i₂ := b2e35 (M.op X2 X2) x
             grind)
          | exact superpose b2e35 b2e63
          | exact resolve b2e63 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e63
        have b2e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e77 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op x X0)) = (M.op X1 (M.op x (M.op x X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 (M.op x X0) X2
             have i₂ := b2e37 X0 (M.op x X0)
             grind)
          | exact superpose b2e37 b2e12
          | exact resolve b2e12 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e89 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op (M.op (M.op X0 X0) X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e67 (M.op X0 X0)
             have i₂ := b2e12 (M.op X0 X0) X0 X1
             grind)
          | exact superpose b2e12 b2e67
          | exact resolve b2e67 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e91 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op x (M.op x (M.op x X0))) := by
          intro X0
          first
          | (have i₁ := b2e67 (M.op x X0)
             have i₂ := b2e37 X0 (M.op x X0)
             grind)
          | exact superpose b2e37 b2e67
          | exact resolve b2e67 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e100 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e89 X0 x
             have i₂ := b2e29 X0 X0 x X0
             grind)
          | exact superpose b2e29 b2e89
          | exact resolve b2e89 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e89
        have b2e101 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e100 X0
             have i₂ := b2e67 X0
             grind)
          | (have i₁ := b2e100 X0
             have i₂ := b2e67 (M.op X0 X0)
             grind)
          | exact superpose b2e67 b2e100
          | exact resolve b2e100 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67 b2e100
        have b2e713 : (M.op x y) = (M.op x (M.op x y)) := by
          first
          | (have i₁ := b2e101 y
             have i₂ := b2e28 y
             grind)
          | exact superpose b2e28 b2e101
          | exact resolve b2e101 b2e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e101
        have b2e816 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
          first
          | (have i₁ := b2e15 (M.op x y) x
             have i₂ := b2e713
             grind)
          | exact superpose b2e713 b2e15
          | (have j0 := b2e15 (M.op x y) x
             grind)
          | (have r₁ := b2e15 (M.op x y) x
             have r₂ := b2e713
             grind)
          | exact resolve b2e15 b2e713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e824 : (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by grind
        clear b2e816
        have b2e826 : (k (M.op x y) x) = (M.op x (M.op x (M.op x y))) := by
          first
          | (have i₁ := b2e824
             have i₂ := b2e77 y x y
             grind)
          | exact superpose b2e77 b2e824
          | exact resolve b2e824 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77 b2e824
        have b2e828 : (M.op x (M.op x y)) = (k (M.op x y) x) := by
          first
          | (have i₁ := b2e826
             have i₂ := b2e91 y
             grind)
          | exact superpose b2e91 b2e826
          | exact resolve b2e826 b2e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e91 b2e826
        have b2e829 : (M.op x y) = (k (M.op x y) x) := by
          first
          | (have i₁ := b2e828
             have i₂ := b2e713
             grind)
          | exact superpose b2e713 b2e828
          | exact resolve b2e828 b2e713
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e713 b2e828
        have b2e1994 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e70 x y
             grind)
          | exact superpose b2e70 b2e21
          | (have j1 := b2e70 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e70 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e70 y x
             grind)
          | exact resolve b2e21 b2e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70
        have b2e2012 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e1994
        have b2e2033 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e2012
             have r₂ := b2e22
             grind)
          | exact resolve b2e2012 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2012
        have b2e2048 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2033
             grind)
          | exact superpose b2e2033 b2e22
          | exact resolve b2e22 b2e2033
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2033
        have b2e2163 : (σ y) ≠ (σ y) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b2e2048
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e2048
          | exact resolve b2e2048 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e2165 : y = (M.op x y) := by grind
        clear b2e2163
        have b2e2487 : y = (k y x) := by
          first
          | (have i₁ := b2e829
             have i₂ := b2e2165
             grind)
          | exact superpose b2e2165 b2e829
          | exact resolve b2e829 b2e2165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e829 b2e2165
        have b2e2993 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e2048
             have i₂ := b2e2487
             grind)
          | exact superpose b2e2487 b2e2048
          | exact resolve b2e2048 b2e2487
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2048 b2e2487
        have b2e2996 : False := by grind
        exact b2e2996
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b3e47 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b3e43
        have b3e49 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e47
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e47
          | exact resolve b3e47 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e54 : y ≠ y ∨ x = (M.op y x) ∨ x = (k x y) := by
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
        have b3e56 : x = (M.op y x) ∨ x = (k x y) := by grind
        clear b3e54
        have b3e59 : x = (k x y) := by
          first
          | (have r₁ := b3e56
             have r₂ := b3e20
             grind)
          | exact resolve b3e56 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e102 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e15
          | exact resolve b3e15 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e105 : (σ x) ≠ (σ x) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e102
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e102
          | exact resolve b3e102 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e106 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e105
        have b3e109 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e106
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e106
          | exact resolve b3e106 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e110 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e109
             have i₂ := b3e59
             grind)
          | exact superpose b3e59 b3e109
          | exact resolve b3e109 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e109
        have b3e114 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e110
             grind)
          | exact superpose b3e110 b3e13
          | exact resolve b3e13 b3e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e110
        have b3e116 : x = (k x x) := by
          first
          | (have i₁ := b3e114
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e114
          | exact resolve b3e114 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e114
        have b3e164 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e116
             grind)
          | exact superpose b3e116 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e165 : x = (M.op x x) := by grind
        clear b3e164
        have b3e187 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b3e32 x
             have i₂ := b3e165
             grind)
          | exact superpose b3e165 b3e32
          | exact resolve b3e32 b3e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e193 : x = (M.op y x) := by
          first
          | (have i₁ := b3e187
             have i₂ := b3e165
             grind)
          | exact superpose b3e165 b3e187
          | exact resolve b3e187 b3e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e165 b3e187
        have b3e194 : False := by grind
        exact b3e194
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e25
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e25
            | exact resolve b4e25 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25
          have b4e27 : False := by grind
          exact b4e27
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : y ≠ y ∨ x = (M.op y x) ∨ x = (k x y) := by
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
          have b5e53 : x = (M.op y x) ∨ x = (k x y) := by grind
          clear b5e49
          have b5e55 : x = (k x y) := by
            first
            | (have r₁ := b5e53
               have r₂ := b5e21
               grind)
            | exact resolve b5e53 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e59 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e2029 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e44119 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e2029 y x
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e2029
            | (have j0 := b5e2029 y x
               grind)
            | exact resolve b5e2029 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55 b5e2029
          have b5e44139 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e44119
          have b5e44156 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e44139
               have r₂ := b5e24
               grind)
            | exact resolve b5e44139 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44139
          have b5e44160 : False := by grind
          exact b5e44160
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 X2 X3
             have i₂ := b6e12 X0 X2 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X2) X3 X1
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e40 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e37
        have b6e42 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e40
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e40
          | exact resolve b6e40 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e51 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        clear b6e51
        have b6e55 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e56 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ (k x y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ x) X1
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e15
          | exact resolve b6e15 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e62 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e84 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e26 (σ y) X0 X1 (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e26
          | exact resolve b6e26 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e312 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op X0 X0)) X1) = (M.op (σ x) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e84 x (M.op X1 X1)
             have i₂ := b6e30 (σ y) X0 x X1
             grind)
          | exact superpose b6e30 b6e84
          | exact resolve b6e84 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e353 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ x) (M.op X1 X1)) := by
          intro X1
          first
          | (have i₁ := b6e312 x X1
             have i₂ := b6e84 (M.op x x) X1
             grind)
          | exact superpose b6e84 b6e312
          | exact resolve b6e312 b6e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84 b6e312
        have b6e665 : (σ (k x y)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e353 (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e353
          | exact resolve b6e353 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e353
        have b6e1876 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e62 x x
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e62
          | exact resolve b6e62 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e62
        have b6e1943 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
        clear b6e1876
        have b6e1959 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e1943
             have r₂ := b6e60
             grind)
          | exact resolve b6e1943 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e1943
        have b6e1984 : (σ (k x x)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e1959
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e1959
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e1959 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2001 : (σ (k x x)) = (σ (M.op y x)) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e1984
             have r₂ := b6e21
             grind)
          | exact resolve b6e1984 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1984
        have b6e2002 : (σ (k x x)) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e2001
             have r₂ := b6e20
             grind)
          | exact resolve b6e2001 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2001
        have b6e2008 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e56 (σ x) (σ y)
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e56
          | exact resolve b6e56 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e56
        have b6e2097 : (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e2008
             have i₂ := b6e665
             grind)
          | exact superpose b6e665 b6e2008
          | exact resolve b6e2008 b6e665
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e665 b6e2008
        have b6e2132 : (M.op (σ y) (σ x)) = (σ (k x x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e2097
             have i₂ := b6e1959
             grind)
          | exact superpose b6e1959 b6e2097
          | exact resolve b6e2097 b6e1959
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1959 b6e2097
        have b6e2158 : (M.op (σ y) (σ x)) = (σ (M.op y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e2132
             have i₂ := b6e2002
             grind)
          | exact superpose b6e2002 b6e2132
          | exact resolve b6e2132 b6e2002
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2002 b6e2132
        have b6e2178 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e2158
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2158
          | exact resolve b6e2158 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2158
        have b6e11012 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e2178
             grind)
          | exact superpose b6e2178 b6e13
          | exact resolve b6e13 b6e2178
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2178
        have b6e11041 : (σ x) = (σ (M.op y x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e11012
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e11012
          | exact resolve b6e11012 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11012
        have b6e11566 : (M.op y x) = (τ (σ x)) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e13 (M.op y x)
             have i₂ := b6e11041
             grind)
          | exact superpose b6e11041 b6e13
          | exact resolve b6e13 b6e11041
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11041
        have b6e11595 : x = (M.op y x) ∨ y = (k y x) := by
          first
          | (have i₁ := b6e11566
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e11566
          | exact resolve b6e11566 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11566
        have b6e11597 : y = (k y x) := by
          first
          | (have r₁ := b6e11595
             have r₂ := b6e20
             grind)
          | exact resolve b6e11595 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11595
        have b6e11789 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e11597
             grind)
          | exact superpose b6e11597 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e11597
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11597
        have b6e11790 : y = (M.op x y) ∨ x = (M.op y x) := by grind
        clear b6e11789
        have b6e11792 : x = (M.op y x) := by
          first
          | (have r₁ := b6e11790
             have r₂ := b6e21
             grind)
          | exact resolve b6e11790 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e11790
        have b6e11794 : False := by grind
        exact b6e11794
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e58 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e62 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e58
          have b7e63 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e23
               grind)
            | exact resolve b7e62 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e64 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e63
            | exact resolve b7e63 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e67 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e64
               grind)
            | exact superpose b7e64 b7e14
            | exact resolve b7e14 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : x = (k x y) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e67
            | exact resolve b7e67 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e79 : x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e80 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b7e79
          have b7e82 : y = (M.op x y) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e21
               grind)
            | exact resolve b7e80 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e84 : False := by grind
          exact b7e84
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e3463 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e72 x y
               grind)
            | exact superpose b8e72 b8e23
            | (have j1 := b8e72 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e72 x y
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e72 y x
               grind)
            | exact resolve b8e23 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e3490 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e3463
          have b8e3515 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have r₁ := b8e3490
               have r₂ := b8e24
               grind)
            | exact resolve b8e3490 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3490
          have b8e3532 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3515
               grind)
            | exact superpose b8e3515 b8e20
            | exact resolve b8e20 b8e3515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3515
          have b8e3617 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3532
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e3532
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e3532 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3532
          have b8e3618 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e3617
          have b8e3619 : y = (M.op x y) := by
            first
            | (have r₁ := b8e3618
               have r₂ := b8e21
               grind)
            | exact resolve b8e3618 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3618
          have b8e3620 : False := by grind
          exact b8e3620

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_x_pyx_pxy_Equation4502 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4502 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
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
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
          intro X0 X1 X2 X3
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y y) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e41 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 (σ y) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e12
          | exact resolve b0e12 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e43 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 X0 X1 y y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e47 : ∀ X1 : G, (M.op x X1) = (M.op y X1) := by
          intro X1
          first
          | (have i₁ := b0e42 x X1
             have i₂ := b0e43 x X1
             grind)
          | exact superpose b0e43 b0e42
          | exact resolve b0e42 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e42
        have b0e48 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
          intro X1
          first
          | (have i₁ := b0e41 x X1
             have i₂ := b0e43 x X1
             grind)
          | exact superpose b0e43 b0e41
          | exact resolve b0e41 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e41
        have b0e103 : (σ y) = (M.op y (σ y)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e48 (σ y)
             grind)
          | exact superpose b0e48 b0e21
          | exact resolve b0e21 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e228 : ∀ X0 : G, (M.op y (σ y)) = (M.op X0 (M.op y (σ y))) := by
          intro X0
          first
          | (have i₁ := b0e43 X0 (σ y)
             have i₂ := b0e48 (σ y)
             grind)
          | exact superpose b0e48 b0e43
          | exact resolve b0e43 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43 b0e48
        have b0e257 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b0e228 X0
             have i₂ := b0e103
             grind)
          | exact superpose b0e103 b0e228
          | exact resolve b0e228 b0e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e103 b0e228
        have b0e629 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e257 (σ x)
             grind)
          | exact superpose b0e257 b0e19
          | exact resolve b0e19 b0e257
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e257
        have b0e634 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e629
             have i₂ := b0e47 y
             grind)
          | exact superpose b0e47 b0e629
          | exact resolve b0e629 b0e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e47 b0e629
        have b0e642 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b0e634
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e634
          | exact resolve b0e634 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e634
        have b0e643 : False := by grind
        exact b0e643
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e43 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) y) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X0 y X1 X2
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e48 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 X1 (σ y) (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e49 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 X1 y y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e53 : ∀ X1 : G, (M.op (σ y) X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b1e48 x X1
               have i₂ := b1e49 x X1
               grind)
            | exact superpose b1e49 b1e48
            | exact resolve b1e48 b1e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e48
          have b1e67 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b1e22
               have i₂ := b1e53 (σ y)
               grind)
            | exact superpose b1e53 b1e22
            | exact resolve b1e22 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e120 : ∀ X0 X3 : G, (M.op X0 y) = (M.op X3 y) := by
            intro X0 X3
            first
            | (have i₁ := b1e43 X3 x x
               have i₂ := b1e43 X0 x x
               grind)
            | (have i₁ := b1e43 X0 x x
               have i₂ := b1e43 (M.op x x) x x
               grind)
            | exact superpose b1e43 b1e43
            | exact resolve b1e43 b1e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e43
          have b1e165 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e24
               have i₂ := b1e120 y X0
               grind)
            | (have i₁ := b1e24
               have i₂ := b1e120 X0 y
               grind)
            | exact superpose b1e120 b1e24
            | exact resolve b1e24 b1e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e120
          have b1e181 : ∀ X0 : G, (M.op y (σ y)) = (M.op X0 (M.op y (σ y))) := by
            intro X0
            first
            | (have i₁ := b1e49 X0 (σ y)
               have i₂ := b1e53 (σ y)
               grind)
            | exact superpose b1e53 b1e49
            | exact resolve b1e49 b1e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49 b1e53
          have b1e204 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e181 X0
               have i₂ := b1e67
               grind)
            | exact superpose b1e67 b1e181
            | exact resolve b1e181 b1e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e67 b1e181
          have b1e250 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e204 (σ x)
               grind)
            | exact superpose b1e204 b1e20
            | exact resolve b1e20 b1e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e204
          have b1e254 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e250
               have i₂ := b1e165 x
               grind)
            | exact superpose b1e165 b1e250
            | exact resolve b1e250 b1e165
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e165 b1e250
          have b1e255 : False := by grind
          exact b1e255
        · have b2e21 : y = (M.op y y) := by grind
          have b2e24 : y ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e25 : False := by grind
          exact b2e25
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e21 : y = (M.op y y) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b3e16 X0 y
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e16
            | (have j0 := b3e16 X0 y
               grind)
            | (have r₁ := b3e16 X0 y
               have r₂ := b3e21
               grind)
            | exact resolve b3e16 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e30 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b3e25 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25
          have b3e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b3e19 (τ X0) X1
               have i₂ := b3e15 X0
               grind)
            | exact superpose b3e15 b3e19
            | exact resolve b3e19 b3e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e90 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b3e22
               have i₂ := b3e18 (σ y) X0
               grind)
            | exact superpose b3e18 b3e22
            | (have j1 := b3e18 X0 X0
               grind)
            | (have r₁ := b3e22
               have r₂ := b3e18 X0 (σ y)
               grind)
            | (have r₁ := b3e22
               have r₂ := b3e18 (σ y) x
               grind)
            | exact resolve b3e22 b3e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e96 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have j0 := b3e90 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e90
          have b3e404 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b3e31 X0 y
               have i₂ := b3e30 (τ X0)
               grind)
            | exact superpose b3e30 b3e31
            | exact resolve b3e31 b3e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e30 b3e31
          have b3e408 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b3e404 X0
               have i₂ := b3e15 X0
               grind)
            | exact superpose b3e15 b3e404
            | exact resolve b3e404 b3e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e404
          have b3e1499 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e408 (σ y)
               have i₂ := b3e96 (σ y)
               grind)
            | exact superpose b3e96 b3e408
            | (have j1 := b3e96 (σ y)
               grind)
            | exact resolve b3e408 b3e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e96 b3e408
          have b3e1503 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b3e1499
          have b3e1507 : False := by grind
          exact b3e1507
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b4e17 X0 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e17
              | (have j0 := b4e17 X0 y
                 grind)
              | (have r₁ := b4e17 X0 y
                 have r₂ := b4e26
                 grind)
              | exact resolve b4e17 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b4e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e27
            have b4e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b4e20 (τ X0) X1
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e20
              | exact resolve b4e20 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e80 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b4e23
                 have i₂ := b4e19 (σ y) X0
                 grind)
              | exact superpose b4e19 b4e23
              | (have j1 := b4e19 X0 X0
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 X0 (σ y)
                 grind)
              | (have r₁ := b4e23
                 have r₂ := b4e19 (σ y) x
                 grind)
              | exact resolve b4e23 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e86 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have j0 := b4e80 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e80
            have b4e192 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b4e31 X0 y
                 have i₂ := b4e30 (τ X0)
                 grind)
              | exact superpose b4e30 b4e31
              | exact resolve b4e31 b4e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30 b4e31
            have b4e200 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b4e192 X0
                 have i₂ := b4e16 X0
                 grind)
              | exact superpose b4e16 b4e192
              | exact resolve b4e192 b4e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e192
            have b4e932 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b4e200 (σ y)
                 have i₂ := b4e86 (σ y)
                 grind)
              | exact superpose b4e86 b4e200
              | (have j1 := b4e86 (σ y)
                 grind)
              | exact resolve b4e200 b4e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e86 b4e200
            have b4e937 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b4e932
            have b4e943 : False := by grind
            exact b4e943
          · have b5e22 : y = (M.op y y) := by grind
            have b5e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e27 : False := by grind
            exact b5e27
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e26 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b6e16 X0 x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e16
            | (have j0 := b6e16 X0 x
               grind)
            | (have r₁ := b6e16 X0 x
               have r₂ := b6e24
               grind)
            | exact resolve b6e16 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e27 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b6e26 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e26
          have b6e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b6e19 (τ X0) X1
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e19
            | exact resolve b6e19 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e128 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 (σ x) X0
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 X0 X0
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 X0 (σ x)
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) x
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e132 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b6e128 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e128
          have b6e381 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e29 X0 x
               have i₂ := b6e27 (τ X0)
               grind)
            | exact superpose b6e27 b6e29
            | exact resolve b6e29 b6e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e27 b6e29
          have b6e388 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e381 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e381
            | exact resolve b6e381 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e381
          have b6e1137 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e388 (σ x)
               have i₂ := b6e132 (σ x)
               grind)
            | exact superpose b6e132 b6e388
            | (have j1 := b6e132 (σ x)
               grind)
            | exact resolve b6e388 b6e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e132 b6e388
          have b6e1141 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b6e1137
          have b6e1145 : False := by grind
          exact b6e1145
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e27 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b7e17 X0 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e17
              | (have j0 := b7e17 X0 y
                 grind)
              | (have r₁ := b7e17 X0 y
                 have r₂ := b7e26
                 grind)
              | exact resolve b7e17 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e28 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b7e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e27
            have b7e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b7e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e29 X0 y
                 have i₂ := b7e28 (τ X0)
                 grind)
              | exact superpose b7e28 b7e29
              | exact resolve b7e29 b7e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e28 b7e29
            have b7e36 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b7e32 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e32
              | exact resolve b7e32 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32
            have b7e80 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b7e23
                 have i₂ := b7e19 (σ y) X0
                 grind)
              | exact superpose b7e19 b7e23
              | (have j1 := b7e19 X0 X0
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 X0 (σ y)
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e19 (σ y) x
                 grind)
              | exact resolve b7e23 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e88 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have j0 := b7e80 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e80
            have b7e829 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e36 (σ y)
                 have i₂ := b7e88 (σ y)
                 grind)
              | exact superpose b7e88 b7e36
              | (have j1 := b7e88 (σ y)
                 grind)
              | exact resolve b7e36 b7e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e36 b7e88
            have b7e832 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b7e829
            have b7e836 : False := by grind
            exact b7e836
          · have b8e22 : y = (M.op y y) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e27 : False := by grind
            exact b8e27
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
            intro X0 X1 X2 X3
            grind
          have b9e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b9e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e21 : y ≠ (M.op y y) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ y)) := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e39 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b9e13 X3 (M.op X2 X2) X4 X5
               have i₂ := b9e13 (M.op X2 X2) X2 X0 X1
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 X1 (σ y) (σ y)
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e13
            | exact resolve b9e13 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e47 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X0 X1 x x
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e51 : ∀ X1 : G, (M.op (σ y) X1) = (M.op x X1) := by
            intro X1
            first
            | (have i₁ := b9e46 x X1
               have i₂ := b9e47 x X1
               grind)
            | exact superpose b9e47 b9e46
            | exact resolve b9e46 b9e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e46
          have b9e52 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op x X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e39 X0 X1 X2 X3 x x
               have i₂ := b9e47 (M.op x x) X2
               grind)
            | exact superpose b9e47 b9e39
            | exact resolve b9e39 b9e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e39
          have b9e61 : (σ y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b9e23
               have i₂ := b9e51 (σ y)
               grind)
            | exact superpose b9e51 b9e23
            | exact resolve b9e23 b9e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e75 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e17 X0 X1
               have i₂ := b9e18 X2 X0
               grind)
            | exact superpose b9e18 b9e17
            | (have j0 := b9e17 X0 X1
               have j1 := b9e18 X1 X1
               grind)
            | (have r₁ := b9e17 X1 X1
               have r₂ := b9e18 X0 X1
               grind)
            | (have r₁ := b9e17 X0 X1
               have r₂ := b9e18 X0 X1
               grind)
            | exact resolve b9e17 b9e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e97 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b9e75 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e75
          have b9e178 : ∀ X0 : G, (M.op x (σ y)) = (M.op X0 (M.op x (σ y))) := by
            intro X0
            first
            | (have i₁ := b9e47 X0 (σ y)
               have i₂ := b9e51 (σ y)
               grind)
            | exact superpose b9e51 b9e47
            | exact resolve b9e47 b9e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e51
          have b9e185 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op X2 X3) X0) := by
            intro X0 X2 X3
            first
            | (have i₁ := b9e13 x X0 X2 X3
               have i₂ := b9e47 x X0
               grind)
            | exact superpose b9e47 b9e13
            | exact resolve b9e13 b9e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e47
          have b9e201 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e178 X0
               have i₂ := b9e61
               grind)
            | exact superpose b9e61 b9e178
            | exact resolve b9e178 b9e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e61 b9e178
          have b9e613 : ∀ X0 X1 X2 X3 : G, (M.op x X0) ≠ (M.op (M.op X1 X2) X0) ∨ (M.op X3 X3) = X3 ∨ (k (M.op (M.op X1 X2) X0) X3) = (M.op X3 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e17 (M.op (M.op X1 X2) X0) X3
               have i₂ := b9e52 X1 X2 X0 (M.op (M.op X1 X2) X0)
               grind)
            | exact superpose b9e52 b9e17
            | (have j0 := b9e17 (M.op (M.op X1 X2) X0) X3
               grind)
            | exact resolve b9e17 b9e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e630 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = X3 ∨ (k (M.op (M.op X1 X2) X0) X3) = (M.op X3 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have j0 := b9e613 X0 X1 X2 X3
               grind)
            | (have r₁ := b9e613 X0 X2 X3 X3
               have r₂ := b9e185 X0 X2 X3
               grind)
            | exact resolve b9e613 b9e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e613
          have b9e648 : ∀ X0 X1 X2 X3 : G, (M.op x X0) = (k (M.op (M.op X1 X2) X0) X3) ∨ (M.op X3 X3) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b9e630 X0 X1 X2 X3
               have i₂ := b9e52 X1 X2 X0 X3
               grind)
            | exact superpose b9e52 b9e630
            | (have j0 := b9e630 X0 X1 X2 X3
               grind)
            | exact resolve b9e630 b9e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e52 b9e630
          have b9e653 : ∀ X0 X3 : G, (M.op x X0) = (k (M.op x X0) X3) ∨ (M.op X3 X3) = X3 := by
            intro X0 X3
            first
            | (have i₁ := b9e648 X0 x x X3
               have i₂ := b9e185 X0 x x
               grind)
            | exact superpose b9e185 b9e648
            | (have j0 := b9e648 X0 x x X3
               grind)
            | exact resolve b9e648 b9e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e185 b9e648
          have b9e654 : ∀ X0 X3 : G, (M.op x X0) = (k (M.op x X0) X3) := by
            intro X0 X3
            first
            | (have j0 := b9e653 X0 X3
               have j1 := b9e16 (M.op x X0) X3
               grind)
            | (have r₁ := b9e653 X0 x
               have r₂ := b9e16 X0 x
               grind)
            | exact resolve b9e653 b9e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e653
          have b9e3063 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b9e654 (σ y) x
               have i₂ := b9e201 x
               grind)
            | exact superpose b9e201 b9e654
            | exact resolve b9e654 b9e201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e201 b9e654
          have b9e3308 : ∀ X0 : G, (σ y) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b9e19 y X0
               have i₂ := b9e3063 (σ X0)
               grind)
            | exact superpose b9e3063 b9e19
            | exact resolve b9e19 b9e3063
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3063
          have b9e3819 : ∀ X0 : G, (k y X0) = (τ (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e14 (k y X0)
               have i₂ := b9e3308 X0
               grind)
            | exact superpose b9e3308 b9e14
            | exact resolve b9e14 b9e3308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3308
          have b9e3820 : ∀ X0 : G, y = (k y X0) := by
            intro X0
            first
            | (have i₁ := b9e3819 X0
               have i₂ := b9e14 y
               grind)
            | exact superpose b9e14 b9e3819
            | exact resolve b9e3819 b9e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3819
          have b9e4445 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e97 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e97
          have b9e4446 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b9e4445 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e4445
          have b9e4447 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b9e4446 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e4446
          have b9e7765 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b9e3820 y
               have i₂ := b9e4447 y
               grind)
            | exact superpose b9e4447 b9e3820
            | (have j1 := b9e4447 y
               grind)
            | exact resolve b9e3820 b9e4447
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e3820 b9e4447
          have b9e7767 : y = (M.op y y) := by grind
          clear b9e7765
          have b9e7831 : False := by grind
          exact b9e7831
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e23 : x = (M.op x x) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e27 : False := by grind
            exact b10e27
          · have b11e23 : x = (M.op x x) := by grind
            have b11e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e27 : False := by grind
            exact b11e27
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
              intro X0 X1 X2 X3
              grind
            have b12e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : y ≠ (M.op y y) := by grind
            have b12e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ x)) := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 (τ X0) X1
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e20
              | exact resolve b12e20 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 X1 (σ x) (σ x)
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e14
              | exact resolve b12e14 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e43 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X0 X1 x x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e44 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 X0 X1 x x
                 have i₂ := b12e14 X2 X1 x x
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e47 : ∀ X1 : G, (M.op (σ x) X1) = (M.op x X1) := by
              intro X1
              first
              | (have i₁ := b12e42 x X1
                 have i₂ := b12e43 x X1
                 grind)
              | exact superpose b12e43 b12e42
              | exact resolve b12e42 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e42
            have b12e52 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e47 (σ y)
                 grind)
              | exact superpose b12e47 b12e21
              | exact resolve b12e21 b12e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e47
            have b12e84 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e17 X1 X0
                 have i₂ := b12e19 X0 X2
                 grind)
              | exact superpose b12e19 b12e17
              | (have j0 := b12e17 X1 X0
                 have j1 := b12e19 X2 X2
                 grind)
              | (have r₁ := b12e17 X0 X1
                 have r₂ := b12e19 X0 X1
                 grind)
              | (have r₁ := b12e17 X0 X0
                 have r₂ := b12e19 X0 X1
                 grind)
              | exact resolve b12e17 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e85 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 X2) X0) ∨ (M.op X3 X3) = X3 ∨ (k (M.op X0 X0) X3) = (M.op (M.op X0 X0) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e14 (M.op X0 X0) X0 X1 X2
                 have i₂ := b12e19 (M.op X0 X0) X3
                 grind)
              | exact superpose b12e19 b12e14
              | (have j1 := b12e19 X3 X3
                 grind)
              | exact resolve b12e14 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e88 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b12e24
                 have i₂ := b12e19 (σ y) X0
                 grind)
              | exact superpose b12e19 b12e24
              | (have j1 := b12e19 X0 X0
                 grind)
              | (have r₁ := b12e24
                 have r₂ := b12e19 X0 (σ y)
                 grind)
              | (have r₁ := b12e24
                 have r₂ := b12e19 (σ y) x
                 grind)
              | exact resolve b12e24 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e93 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have j0 := b12e88 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e88
            have b12e94 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
              intro X0 X1 X2
              first
              | (have j0 := b12e84 X0 X1 X2
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e84
            have b12e137 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op X2 X3) X0) := by
              intro X0 X2 X3
              first
              | (have i₁ := b12e14 x X0 X2 X3
                 have i₂ := b12e43 x X0
                 grind)
              | exact superpose b12e43 b12e14
              | exact resolve b12e14 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e140 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op x X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e18 (M.op X0 X0) X1
                 have i₂ := b12e43 (M.op X0 X0) X0
                 grind)
              | exact superpose b12e43 b12e18
              | (have j0 := b12e18 (M.op X0 X0) X1
                 grind)
              | (have r₁ := b12e18 (M.op x x) X1
                 have r₂ := b12e43 (M.op x x) x
                 grind)
              | exact resolve b12e18 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e149 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k (M.op X0 X0) X1) ∨ (M.op X1 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b12e140 X0 X1
                 have i₂ := b12e43 X1 X0
                 grind)
              | exact superpose b12e43 b12e140
              | (have j0 := b12e140 X0 X1
                 grind)
              | exact resolve b12e140 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43 b12e140
            have b12e873 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e44 X0 X0 X2
                 have i₂ := b12e93 X0
                 grind)
              | exact superpose b12e93 b12e44
              | (have j1 := b12e93 X0
                 grind)
              | exact resolve b12e44 b12e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e44
            have b12e1557 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X3) = X2 ∨ (k X3 X0) = (M.op X3 X0) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e17 X1 X0
                 have i₂ := b12e94 X3 X2 X0
                 grind)
              | exact superpose b12e94 b12e17
              | (have j0 := b12e17 X1 X0
                 have j1 := b12e94 X3 X2 X0
                 grind)
              | (have r₁ := b12e17 X0 X2
                 have r₂ := b12e94 X0 X1 X2
                 grind)
              | exact resolve b12e17 b12e94
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e94
            have b12e1608 : ∀ X0 X1 X2 X3 : G, (k X1 X0) = X1 ∨ (k X2 X3) = X2 ∨ (k X3 X0) = (M.op X3 X0) := by
              intro X0 X1 X2 X3
              first
              | (have j0 := b12e1557 X0 X1 X2 X3
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1557
            have b12e5411 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X0 X1) X2) = X2 ∨ (M.op X3 X3) = (M.op (M.op X4 X5) X3) ∨ (k (M.op X3 X3) X2) = (M.op (M.op X3 X3) X2) ∨ (M.op X6 X6) = X6 ∨ (k (M.op X2 X2) X6) = (M.op (M.op X2 X2) X6) := by
              intro X0 X1 X2 X3 X4 X5 X6
              first
              | (have i₁ := b12e85 X3 X4 X5 X2
                 have i₂ := b12e85 X2 X0 X1 X6
                 grind)
              | (have i₁ := b12e85 X0 X1 X2 (M.op X1 X2)
                 have i₂ := b12e85 (M.op X1 X2) X1 X2 X3
                 grind)
              | exact superpose b12e85 b12e85
              | (have j0 := b12e85 X3 X4 X5 X6
                 have j1 := b12e85 X3 X4 X5 X6
                 grind)
              | exact resolve b12e85 b12e85
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e5667 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
              intro X0 X1 X2
              first
              | (have j0 := b12e85 X0 X1 X2 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e85
            have b12e5680 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) X0) = (M.op (M.op X0 X0) X0) := by
              intro X0
              first
              | (have i₁ := b12e5667 X0 x x
                 have i₂ := b12e137 X0 x x
                 grind)
              | exact superpose b12e137 b12e5667
              | (have j0 := b12e5667 X0 x x
                 grind)
              | exact resolve b12e5667 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5667
            have b12e5795 : ∀ X2 X3 X4 X5 X6 : G, (M.op x X2) = X2 ∨ (M.op X3 X3) = (M.op (M.op X4 X5) X3) ∨ (k (M.op X3 X3) X2) = (M.op (M.op X3 X3) X2) ∨ (M.op X6 X6) = X6 ∨ (k (M.op X2 X2) X6) = (M.op (M.op X2 X2) X6) := by
              intro X2 X3 X4 X5 X6
              first
              | (have i₁ := b12e5411 x x X2 X3 X4 X5 X6
                 have i₂ := b12e137 X2 x x
                 grind)
              | exact superpose b12e137 b12e5411
              | (have j0 := b12e5411 x x X2 X3 X4 X5 X6
                 grind)
              | exact resolve b12e5411 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5411
            have b12e5838 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b12e5680 X0
                 have i₂ := b12e137 X0 X0 X0
                 grind)
              | exact superpose b12e137 b12e5680
              | (have j0 := b12e5680 X0
                 grind)
              | exact resolve b12e5680 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5680
            have b12e5931 : ∀ X2 X3 X6 : G, (M.op X3 X3) = (M.op x X3) ∨ (M.op x X2) = X2 ∨ (k (M.op X3 X3) X2) = (M.op (M.op X3 X3) X2) ∨ (M.op X6 X6) = X6 ∨ (k (M.op X2 X2) X6) = (M.op (M.op X2 X2) X6) := by
              intro X2 X3 X6
              first
              | (have i₁ := b12e5795 X2 X3 x x X6
                 have i₂ := b12e137 X3 x x
                 grind)
              | exact superpose b12e137 b12e5795
              | (have j0 := b12e5795 X2 X3 x x X6
                 grind)
              | exact resolve b12e5795 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5795
            have b12e5975 : ∀ X2 X3 X6 : G, (M.op x X2) = (k (M.op X3 X3) X2) ∨ (M.op X3 X3) = (M.op x X3) ∨ (M.op x X2) = X2 ∨ (M.op X6 X6) = X6 ∨ (k (M.op X2 X2) X6) = (M.op (M.op X2 X2) X6) := by
              intro X2 X3 X6
              first
              | (have i₁ := b12e5931 X2 X3 X6
                 have i₂ := b12e137 X2 X3 X3
                 grind)
              | exact superpose b12e137 b12e5931
              | (have j0 := b12e5931 X2 X3 X6
                 grind)
              | exact resolve b12e5931 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5931
            have b12e5980 : ∀ X2 X3 X6 : G, (M.op x X6) = (k (M.op X2 X2) X6) ∨ (M.op x X2) = (k (M.op X3 X3) X2) ∨ (M.op X6 X6) = X6 ∨ (M.op x X2) = X2 ∨ (M.op X3 X3) = (M.op x X3) := by
              intro X2 X3 X6
              first
              | (have i₁ := b12e5975 X2 X3 X6
                 have i₂ := b12e137 X6 X2 X2
                 grind)
              | exact superpose b12e137 b12e5975
              | (have j0 := b12e5975 X2 X3 X6
                 grind)
              | exact resolve b12e5975 b12e137
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e137 b12e5975
            have b12e13525 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e24
                 have i₂ := b12e873 (σ y) (σ y) X0
                 grind)
              | (have i₁ := b12e24
                 have i₂ := b12e873 (σ y) X0 (σ y)
                 grind)
              | exact superpose b12e873 b12e24
              | (have j1 := b12e873 (σ y) x x
                 grind)
              | exact resolve b12e24 b12e873
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e13580 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op (σ y) X1) = (k (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e93 X1
                 have i₂ := b12e873 X1 X1 X0
                 grind)
              | (have i₁ := b12e93 X1
                 have i₂ := b12e873 X1 X0 X1
                 grind)
              | exact superpose b12e873 b12e93
              | (have j0 := b12e93 X1
                 have j1 := b12e873 X1 X1 x
                 grind)
              | exact resolve b12e93 b12e873
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e93 b12e873
            have b12e13747 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) := by
              intro X0 X1
              first
              | (have j0 := b12e13580 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e13580
            have b12e13776 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
              first
              | (have j1 := b12e13747 x (σ y)
                 grind)
              | (have r₁ := b12e13525 x
                 have r₂ := b12e13747 x (σ y)
                 grind)
              | exact resolve b12e13525 b12e13747
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e13525 b12e13747
            have b12e13798 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
              first
              | (have i₁ := b12e13776
                 have i₂ := b12e20 y y
                 grind)
              | exact superpose b12e20 b12e13776
              | exact resolve b12e13776 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e13776
            have b12e13831 : (σ y) ≠ (σ (k y y)) := by
              first
              | (have i₁ := b12e24
                 have i₂ := b12e13798
                 grind)
              | exact superpose b12e13798 b12e24
              | exact resolve b12e24 b12e13798
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e17156 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1
              first
              | (have j0 := b12e1608 X1 X0 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1608
            have b12e17159 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1
              first
              | (have j0 := b12e17156 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e17156
            have b12e22476 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e31 X0 X1
                 have i₂ := b12e17159 (τ X0) X1
                 grind)
              | exact superpose b12e17159 b12e31
              | (have j1 := b12e17159 X0 X1
                 grind)
              | exact resolve b12e31 b12e17159
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e31 b12e17159
            have b12e22560 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e22476 X0 X1
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e22476
              | (have j0 := b12e22476 X0 X1
                 grind)
              | exact resolve b12e22476 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e22476
            have b12e39211 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (M.op X1 X1) = (k X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X0 X1
                 have i₂ := b12e22560 (σ X0) X1
                 grind)
              | exact superpose b12e22560 b12e20
              | (have j1 := b12e22560 X0 X1
                 grind)
              | exact resolve b12e20 b12e22560
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e22560
            have b12e126288 : (σ y) ≠ (σ y) ∨ (M.op y y) = (k y y) := by
              first
              | (have i₁ := b12e13831
                 have i₂ := b12e39211 y y
                 grind)
              | exact superpose b12e39211 b12e13831
              | (have j1 := b12e39211 x y
                 grind)
              | (have r₁ := b12e13831
                 have r₂ := b12e39211 y y
                 grind)
              | exact resolve b12e13831 b12e39211
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e39211
            have b12e126387 : (M.op y y) = (k y y) := by grind
            clear b12e126288
            have b12e786479 : ∀ X0 : G, (M.op x X0) ≠ (M.op x X0) ∨ (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b12e5980 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5980
            have b12e786480 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 ∨ (M.op X0 X0) = (M.op x X0) := by
              intro X0
              first
              | (have j0 := b12e786479 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e786479
            have b12e786796 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have j0 := b12e786480 X0
                 have j1 := b12e149 X0 X0
                 grind)
              | (have r₁ := b12e786480 X0
                 have r₂ := b12e149 X0 x
                 grind)
              | (have r₁ := b12e786480 x
                 have r₂ := b12e149 x x
                 grind)
              | exact resolve b12e786480 b12e149
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e149 b12e786480
            have b12e786798 : ∀ X0 : G, (M.op x X0) = (k (M.op X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b12e786796 X0
                 have j1 := b12e5838 X0
                 grind)
              | (have r₁ := b12e786796 x
                 have r₂ := b12e5838 x
                 grind)
              | (have r₁ := b12e786796 X0
                 have r₂ := b12e5838 X0
                 grind)
              | exact resolve b12e786796 b12e5838
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e5838 b12e786796
            have b12e786808 : (M.op x (σ y)) = (k (σ (k y y)) (σ y)) ∨ (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b12e786798 (σ y)
                 have i₂ := b12e13798
                 grind)
              | exact superpose b12e13798 b12e786798
              | exact resolve b12e786798 b12e13798
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e13798
            have b12e786824 : (M.op x (σ y)) = (k (σ (k y y)) (σ y)) := by
              first
              | (have r₁ := b12e786808
                 have r₂ := b12e13831
                 grind)
              | exact resolve b12e786808 b12e13831
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e13831 b12e786808
            have b12e786825 : (M.op x (σ y)) = (σ (k (k y y) y)) := by
              first
              | (have i₁ := b12e786824
                 have i₂ := b12e20 (k y y) y
                 grind)
              | exact superpose b12e20 b12e786824
              | exact resolve b12e786824 b12e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e786824
            have b12e786826 : (M.op x (σ y)) = (σ (k (M.op y y) y)) := by
              first
              | (have i₁ := b12e786825
                 have i₂ := b12e126387
                 grind)
              | exact superpose b12e126387 b12e786825
              | exact resolve b12e786825 b12e126387
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e126387 b12e786825
            have b12e791395 : (σ (M.op x y)) = (M.op x (σ y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b12e786826
                 have i₂ := b12e786798 y
                 grind)
              | exact superpose b12e786798 b12e786826
              | (have j1 := b12e786798 y
                 grind)
              | exact resolve b12e786826 b12e786798
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e786798 b12e786826
            have b12e791447 : y = (M.op y y) := by
              first
              | (have r₁ := b12e791395
                 have r₂ := b12e52
                 grind)
              | exact resolve b12e791395 b12e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e52 b12e791395
            have b12e791452 : False := by grind
            exact b12e791452
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e24 : x = (M.op x x) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e29 : False := by grind
              exact b13e29
            · have b14e24 : x = (M.op x x) := by grind
              have b14e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e29 : False := by grind
              exact b14e29
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b15e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
            have b15e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e27 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b15e17 X0 x
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e17
              | (have j0 := b15e17 X0 x
                 grind)
              | (have r₁ := b15e17 X0 x
                 have r₂ := b15e26
                 grind)
              | exact resolve b15e17 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e28 : ∀ X0 : G, (k X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e27
            have b15e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
            have b15e32 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
              intro X0
              first
              | (have i₁ := b15e29 X0 x
                 have i₂ := b15e28 (τ X0)
                 grind)
              | exact superpose b15e28 b15e29
              | exact resolve b15e29 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28 b15e29
            have b15e36 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b15e32 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e32
              | exact resolve b15e32 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e32
            have b15e81 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 X0 X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 X0 (σ x)
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) x
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e87 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have j0 := b15e81 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e81
            have b15e753 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b15e36 (σ x)
                 have i₂ := b15e87 (σ x)
                 grind)
              | exact superpose b15e87 b15e36
              | (have j1 := b15e87 (σ x)
                 grind)
              | exact resolve b15e36 b15e87
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e36 b15e87
            have b15e756 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear b15e753
            have b15e760 : False := by grind
            exact b15e760
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e24 : x = (M.op x x) := by grind
              have b16e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e29 : False := by grind
              exact b16e29
            · have b17e24 : x = (M.op x x) := by grind
              have b17e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e29 : False := by grind
              exact b17e29
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e22 : x ≠ (M.op x x) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e25 : False := by grind
          exact b18e25
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e22 : y ≠ (M.op y y) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e27 : False := by grind
            exact b19e27
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
            have b20e26 : y ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e27 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b20e17 X0 (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e17
              | (have j0 := b20e17 X0 (σ y)
                 grind)
              | (have r₁ := b20e17 X0 (σ y)
                 have r₂ := b20e24
                 grind)
              | exact resolve b20e17 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b20e27 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e27
            have b20e32 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b20e28 (σ X0)
                 have i₂ := b20e20 X0 y
                 grind)
              | exact superpose b20e20 b20e28
              | exact resolve b20e28 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e28
            have b20e35 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b20e15 (k X0 y)
                 have i₂ := b20e32 X0
                 grind)
              | exact superpose b20e32 b20e15
              | exact resolve b20e15 b20e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e36 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b20e35 X0
                 have i₂ := b20e15 X0
                 grind)
              | exact superpose b20e15 b20e35
              | exact resolve b20e35 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e35
            have b20e91 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b20e36 X0
                 have i₂ := b20e19 X0 y
                 grind)
              | exact superpose b20e19 b20e36
              | (have j1 := b20e19 y y
                 grind)
              | exact resolve b20e36 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e36
            have b20e99 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b20e91 X0
                 grind)
              | (have r₁ := b20e91 y
                 have r₂ := b20e26
                 grind)
              | (have r₁ := b20e91 X0
                 have r₂ := b20e26
                 grind)
              | exact resolve b20e91 b20e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e91
            have b20e6151 : y ≠ y ∨ y = (M.op y y) := by
              first
              | (have j0 := b20e99 y
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e99
            have b20e6152 : y = (M.op y y) := by grind
            clear b20e6151
            have b20e6160 : False := by grind
            exact b20e6160
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e23 : x ≠ (M.op x x) := by grind
            have b21e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e27 : False := by grind
            exact b21e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e23 : y ≠ (M.op y y) := by grind
              have b22e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e29 : False := by grind
              exact b22e29
            · have b23e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              have b23e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e18 X0 (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have j0 := b23e18 X0 (σ x)
                   grind)
                | (have r₁ := b23e18 X0 (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e30 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b23e29 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e29
              have b23e34 : ∀ X0 : G, (σ X0) = (σ (k X0 x)) := by
                intro X0
                first
                | (have i₁ := b23e21 X0 x
                   have i₂ := b23e30 (σ X0)
                   grind)
                | exact superpose b23e30 b23e21
                | exact resolve b23e21 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e37 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) := by
                intro X0
                first
                | (have i₁ := b23e16 (k X0 x)
                   have i₂ := b23e34 X0
                   grind)
                | exact superpose b23e34 b23e16
                | exact resolve b23e16 b23e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e34
              have b23e38 : ∀ X0 : G, (k X0 x) = X0 := by
                intro X0
                first
                | (have i₁ := b23e37 X0
                   have i₂ := b23e16 X0
                   grind)
                | exact superpose b23e16 b23e37
                | exact resolve b23e37 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e42 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X2 X2)) = (M.op X3 (M.op (M.op X0 X1) X2)) := by
                intro X0 X1 X2 X3 X4 X5
                first
                | (have i₁ := b23e15 X3 (M.op X2 X2) X4 X5
                   have i₂ := b23e15 (M.op X2 X2) X2 X0 X1
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e45 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 X1 (σ x) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e15
                | exact resolve b23e15 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e51 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X0 X1) X2)) = (M.op (σ x) X2) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e42 X0 X1 X2 X3 x x
                   have i₂ := b23e45 (M.op x x) X2
                   grind)
                | exact superpose b23e45 b23e42
                | exact resolve b23e42 b23e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e42
              have b23e86 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b23e25
                   have i₂ := b23e20 (σ y) X0
                   grind)
                | exact superpose b23e20 b23e25
                | (have j1 := b23e20 X0 X0
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 X0 (σ y)
                   grind)
                | (have r₁ := b23e25
                   have r₂ := b23e20 (σ y) x
                   grind)
                | exact resolve b23e25 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e92 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ y) X0) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have j0 := b23e86 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e86
              have b23e135 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X0) = (M.op (σ x) X0) := by
                intro X0 X2 X3
                first
                | (have i₁ := b23e15 x X0 X2 X3
                   have i₂ := b23e45 x X0
                   grind)
                | exact superpose b23e45 b23e15
                | exact resolve b23e15 b23e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e451 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X0) ≠ (M.op (σ x) X0) ∨ (k X3 (M.op (M.op X1 X2) X0)) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e18 X3 (M.op (M.op X1 X2) X0)
                   have i₂ := b23e51 X1 X2 X0 (M.op (M.op X1 X2) X0)
                   grind)
                | exact superpose b23e51 b23e18
                | (have j0 := b23e18 X3 (M.op (M.op X1 X2) X0)
                   grind)
                | exact resolve b23e18 b23e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e468 : ∀ X0 X1 X2 X3 : G, (k X3 (M.op (M.op X1 X2) X0)) = X3 := by
                intro X0 X1 X2 X3
                first
                | (have j0 := b23e451 X0 X1 X2 X3
                   grind)
                | (have r₁ := b23e451 X0 X2 X3 X3
                   have r₂ := b23e135 X0 X2 X3
                   grind)
                | exact resolve b23e451 b23e135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e451
              have b23e480 : ∀ X0 X3 : G, (k X3 (M.op (σ x) X0)) = X3 := by
                intro X0 X3
                first
                | (have i₁ := b23e468 X0 x x X3
                   have i₂ := b23e135 X0 x x
                   grind)
                | exact superpose b23e135 b23e468
                | exact resolve b23e468 b23e135
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e135 b23e468
              have b23e637 : (σ y) = (M.op (σ y) x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e38 (σ y)
                   have i₂ := b23e92 x
                   grind)
                | exact superpose b23e92 b23e38
                | (have j1 := b23e92 x
                   grind)
                | exact resolve b23e38 b23e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e38
              have b23e642 : (σ y) = (M.op (σ y) x) := by
                first
                | (have r₁ := b23e637
                   have r₂ := b23e27
                   grind)
                | exact resolve b23e637 b23e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e637
              have b23e659 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (σ y) X1) := by
                intro X0 X1
                first
                | (have i₁ := b23e15 X0 X1 (σ y) x
                   have i₂ := b23e642
                   grind)
                | exact superpose b23e642 b23e15
                | exact resolve b23e15 b23e642
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e660 : ∀ X1 : G, (M.op (σ x) X1) = (M.op (σ y) X1) := by
                intro X1
                first
                | (have i₁ := b23e659 x X1
                   have i₂ := b23e45 x X1
                   grind)
                | exact superpose b23e45 b23e659
                | exact resolve b23e659 b23e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e45 b23e659
              have b23e5256 : (σ y) = (M.op (σ x) x) := by
                first
                | (have i₁ := b23e642
                   have i₂ := b23e660 x
                   grind)
                | exact superpose b23e660 b23e642
                | exact resolve b23e642 b23e660
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e642 b23e660
              have b23e5742 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b23e480 x X0
                   have i₂ := b23e5256
                   grind)
                | exact superpose b23e5256 b23e480
                | exact resolve b23e480 b23e5256
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e480 b23e5256
              have b23e6407 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b23e92 (σ y)
                   have i₂ := b23e5742 (σ y)
                   grind)
                | exact superpose b23e5742 b23e92
                | (have j0 := b23e92 (σ y)
                   grind)
                | exact resolve b23e92 b23e5742
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e92 b23e5742
              have b23e6422 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b23e6407
              have b23e6435 : False := by grind
              exact b23e6435
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e23 : x ≠ (M.op x x) := by grind
            have b24e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e27 : False := by grind
            exact b24e27
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e23 : y ≠ (M.op y y) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : False := by grind
              exact b25e29
            · have b26e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
                intro X0 X1 X2 X3
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e27 : x ≠ (M.op x x) := by grind
              have b26e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X0 X1 x x
                   have i₂ := b26e15 X2 X1 x x
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e70 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 X0 X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 X0 (σ x)
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) x
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e74 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have j0 := b26e70 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70
              have b26e212 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e36 X0 X0 X2
                   have i₂ := b26e74 X0
                   grind)
                | exact superpose b26e74 b26e36
                | (have j1 := b26e74 X0
                   grind)
                | exact resolve b26e36 b26e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e36
              have b26e17071 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e212 (σ y) (σ y) X0
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e212 (σ y) X0 (σ y)
                   grind)
                | exact superpose b26e212 b26e25
                | (have j1 := b26e212 (σ y) x x
                   grind)
                | exact resolve b26e25 b26e212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e17106 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ x) X1) = (k (σ x) X1) ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e74 X1
                   have i₂ := b26e212 X1 X1 X0
                   grind)
                | (have i₁ := b26e74 X1
                   have i₂ := b26e212 X1 X0 X1
                   grind)
                | exact superpose b26e212 b26e74
                | (have j0 := b26e74 X1
                   have j1 := b26e212 X1 X1 x
                   grind)
                | exact resolve b26e74 b26e212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e74 b26e212
              have b26e17352 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op (σ x) X1) = (k (σ x) X1) := by
                intro X0 X1
                first
                | (have j0 := b26e17106 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17106
              have b26e17378 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j1 := b26e17352 x (σ y)
                   grind)
                | (have r₁ := b26e17071 x
                   have r₂ := b26e17352 x (σ y)
                   grind)
                | exact resolve b26e17071 b26e17352
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17071 b26e17352
              have b26e17386 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e17378
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e17378
                | exact resolve b26e17378 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17378
              have b26e19730 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e17386
                   grind)
                | exact superpose b26e17386 b26e22
                | exact resolve b26e22 b26e17386
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e17386
              have b26e20708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b26e19730
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e19730
                | (have j1 := b26e20 y y
                   grind)
                | exact resolve b26e19730 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19730
              have b26e20718 : y = (M.op y y) ∨ x = (M.op x x) := by grind
              clear b26e20708
              have b26e20722 : x = (M.op x x) := by
                first
                | (have r₁ := b26e20718
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e20718 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e20718
              have b26e20723 : False := by grind
              exact b26e20723

/-- `Equation4520`: `x ◇ (y ◇ z) = (x ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_y_pxy_Equation4520 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4520 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4520.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e30 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 X1)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X0 X1 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2 x
           have i₂ := b0e11 X0 X3 X2 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : y = (M.op y y) := by
        first
        | (have i₁ := b0e36 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e36
        | exact resolve b0e36 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e49 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (k X2 (M.op X0 X3)) = (M.op X2 X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e14 X2 (M.op X0 X3)
           have i₂ := b0e11 X0 X1 X2 X3
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 X2 (M.op X0 X3)
           grind)
        | (have r₁ := b0e14 X2 (M.op X0 (M.op X1 X2))
           have r₂ := b0e11 X0 X1 X2 (M.op X1 X2)
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : y ≠ y ∨ (k x y) = (M.op x x) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : (k x y) = (M.op x x) := by grind
      clear b0e51
      have b0e54 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear b0e50
      have b0e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e54
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e54
        | exact resolve b0e54 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e56 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e55
           have i₂ := b0e53
           grind)
        | exact superpose b0e53 b0e55
        | exact resolve b0e55 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e55
      have b0e135 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e30 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30
        | exact resolve b0e30 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e143 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op X1 (σ x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (σ x) x
           have i₂ := b0e30 X0 x
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e147 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 (σ y)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X0 X1) X2 X3 (σ x)
           have i₂ := b0e30 X0 X1
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e148 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X3) (σ x)) = (M.op X1 (M.op X0 (σ y))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e11 X1 (M.op X0 x) (σ x) X3
           have i₂ := b0e30 X0 x
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X1 (M.op X0 (σ y))) := by
        intro X0 X1
        first
        | (have i₁ := b0e148 X0 X1 x
           have i₂ := b0e30 X1 x
           grind)
        | exact superpose b0e30 b0e148
        | exact resolve b0e148 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148
      have b0e152 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e135
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e135
        | exact resolve b0e135 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e135
      have b0e274 : (M.op (σ y) x) = (M.op (σ y) y) := by
        first
        | (have i₁ := b0e35 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e292 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op X0 (M.op (σ y) y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ y) x X1
           have i₂ := b0e274
           grind)
        | exact superpose b0e274 b0e11
        | exact resolve b0e11 b0e274
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e274
      have b0e346 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X0 X1 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e37
        | exact resolve b0e37 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e347 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X0 X1 y y
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e37
        | exact resolve b0e37 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e2788 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e49 X1 X1 X0 (M.op X2 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e3848 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ x)) (M.op X1 (σ x))) = (k (M.op X1 (σ x)) (M.op X2 (M.op X0 (σ y)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2788 (M.op X1 (σ x)) X2 X0
           have i₂ := b0e143 X0 X1
           grind)
        | exact superpose b0e143 b0e2788
        | exact resolve b0e2788 b0e143
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e143
      have b0e3850 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X1 x)) = (k (M.op X1 x) (M.op X2 (M.op X0 y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e2788 (M.op X1 x) X2 X0
           have i₂ := b0e346 X0 X1
           grind)
        | exact superpose b0e346 b0e2788
        | exact resolve b0e2788 b0e346
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e346 b0e2788
      have b0e3940 : ∀ X1 X2 : G, (M.op (M.op X1 x) (M.op X1 x)) = (k (M.op X1 x) (M.op X2 y)) := by
        intro X1 X2
        first
        | (have i₁ := b0e3850 x X1 X2
           have i₂ := b0e347 X2 x
           grind)
        | exact superpose b0e347 b0e3850
        | exact resolve b0e3850 b0e347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3850
      have b0e3942 : ∀ X1 X2 : G, (M.op (M.op X1 (σ x)) (M.op X1 (σ x))) = (k (M.op X1 (σ x)) (M.op X2 (σ y))) := by
        intro X1 X2
        first
        | (have i₁ := b0e3848 x X1 X2
           have i₂ := b0e149 x X2
           grind)
        | exact superpose b0e149 b0e3848
        | exact resolve b0e3848 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149 b0e3848
      have b0e3962 : ∀ X1 X2 : G, (M.op (M.op X1 (σ y)) x) = (k (M.op X1 x) (M.op X2 y)) := by
        intro X1 X2
        first
        | (have i₁ := b0e3940 X1 X2
           have i₂ := b0e147 X1 x X1 x
           grind)
        | exact superpose b0e147 b0e3940
        | exact resolve b0e3940 b0e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3940
      have b0e3964 : ∀ X1 X2 : G, (M.op (M.op X1 (σ y)) (σ x)) = (k (M.op X1 (σ x)) (M.op X2 (σ y))) := by
        intro X1 X2
        first
        | (have i₁ := b0e3942 X1 X2
           have i₂ := b0e147 X1 (σ x) X1 (σ x)
           grind)
        | exact superpose b0e147 b0e3942
        | exact resolve b0e3942 b0e147
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147 b0e3942
      have b0e3972 : ∀ X1 X2 : G, (M.op X1 (M.op (σ y) y)) = (k (M.op X1 x) (M.op X2 y)) := by
        intro X1 X2
        first
        | (have i₁ := b0e3962 X1 X2
           have i₂ := b0e292 X1 (σ y)
           grind)
        | exact superpose b0e292 b0e3962
        | exact resolve b0e3962 b0e292
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e292 b0e3962
      have b0e3974 : ∀ X1 X2 : G, (M.op X1 (σ y)) = (k (M.op X1 (σ x)) (M.op X2 (σ y))) := by
        intro X1 X2
        first
        | (have i₁ := b0e3964 X1 X2
           have i₂ := b0e30 X1 (σ y)
           grind)
        | exact superpose b0e30 b0e3964
        | exact resolve b0e3964 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30 b0e3964
      have b0e3976 : ∀ X1 X2 : G, (M.op X1 y) = (k (M.op X1 x) (M.op X2 y)) := by
        intro X1 X2
        first
        | (have i₁ := b0e3972 X1 X2
           have i₂ := b0e347 X1 (σ y)
           grind)
        | exact superpose b0e347 b0e3972
        | exact resolve b0e3972 b0e347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e347 b0e3972
      have b0e9577 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 x) y) := by
        intro X0
        first
        | (have i₁ := b0e3976 X0 y
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e3976
        | exact resolve b0e3976 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e3976
      have b0e20188 : ∀ X0 : G, (M.op X0 (σ y)) = (k (M.op X0 (σ x)) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e3974 X0 (σ y)
           have i₂ := b0e152
           grind)
        | exact superpose b0e152 b0e3974
        | exact resolve b0e3974 b0e152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e152 b0e3974
      have b0e20399 : (M.op (σ x) (σ y)) = (k (σ (M.op x x)) (σ y)) := by
        first
        | (have i₁ := b0e20188 (σ x)
           have i₂ := b0e56
           grind)
        | exact superpose b0e56 b0e20188
        | exact resolve b0e20188 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56 b0e20188
      have b0e20427 : (M.op (σ x) (σ y)) = (σ (k (M.op x x) y)) := by
        first
        | (have i₁ := b0e20399
           have i₂ := b0e17 (M.op x x) y
           grind)
        | exact superpose b0e17 b0e20399
        | exact resolve b0e20399 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20399
      have b0e20449 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e20427
           have i₂ := b0e9577 x
           grind)
        | exact superpose b0e9577 b0e20427
        | exact resolve b0e20427 b0e9577
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9577 b0e20427
      have b0e20459 : False := by grind
      exact b0e20459
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b1e28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 (σ x) (σ x) X1
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ x) X0 X1 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y X0 X1 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (M.op y (σ x)) = (M.op y (σ y)) := by
          first
          | (have i₁ := b1e34 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e34
          | exact resolve b1e34 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : y = (M.op y y) := by
          first
          | (have i₁ := b1e34 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e49 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b1e51 : (k x y) = (M.op x x) := by grind
        clear b1e49
        have b1e53 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e40
             grind)
          | exact resolve b1e15 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e56 : y = (k y y) := by grind
        clear b1e53
        have b1e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e77 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        have b1e80 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e77
             have r₂ := b1e21
             grind)
          | exact resolve b1e77 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e81 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e80
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e80
          | exact resolve b1e80 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e82 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e81
             have i₂ := b1e51
             grind)
          | exact superpose b1e51 b1e81
          | exact resolve b1e81 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e81
        have b1e87 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e82
             grind)
          | exact superpose b1e82 b1e13
          | exact resolve b1e13 b1e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e88 : y = (M.op x x) := by
          first
          | (have i₁ := b1e87
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e87
          | exact resolve b1e87 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e93 : ∀ X0 X1 : G, (M.op y X1) = (M.op x (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 x X0 X1 x
             have i₂ := b1e88
             grind)
          | exact superpose b1e88 b1e12
          | exact resolve b1e12 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e119 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e28 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e28
          | exact resolve b1e28 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e260 : y = (M.op x y) := by
          first
          | (have i₁ := b1e93 y y
             have i₂ := b1e40
             grind)
          | exact superpose b1e40 b1e93
          | exact resolve b1e93 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40 b1e93
        have b1e292 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op y (σ y))) := by
          first
          | (have i₁ := b1e33 y (σ x)
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e33
          | exact resolve b1e33 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e312 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e292
             have i₂ := b1e33 y (σ y)
             grind)
          | exact superpose b1e33 b1e292
          | exact resolve b1e292 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33 b1e292
        have b1e3820 : (σ (M.op x y)) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e119
             grind)
          | exact superpose b1e119 b1e19
          | exact resolve b1e19 b1e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3823 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ x)
             have i₂ := b1e119
             grind)
          | exact superpose b1e119 b1e15
          | (have j0 := b1e15 (σ y) (σ x)
             grind)
          | exact resolve b1e15 b1e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e3866 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e3823
             have i₂ := b1e312
             grind)
          | exact superpose b1e312 b1e3823
          | exact resolve b1e3823 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3823
        have b1e3869 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e3820
             have i₂ := b1e312
             grind)
          | exact superpose b1e312 b1e3820
          | exact resolve b1e3820 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3820
        have b1e3879 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e3866
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e3866
          | exact resolve b1e3866 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3866
        have b1e3880 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e3869
             have i₂ := b1e260
             grind)
          | exact superpose b1e260 b1e3869
          | exact resolve b1e3869 b1e260
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e260 b1e3869
        have b1e4415 : (σ x) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e119
             have i₂ := b1e62 y x
             grind)
          | exact superpose b1e62 b1e119
          | (have j1 := b1e62 y x
             grind)
          | exact resolve b1e119 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e119
        have b1e4471 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e4415
             have i₂ := b1e312
             grind)
          | exact superpose b1e312 b1e4415
          | exact resolve b1e4415 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4415
        have b1e4472 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
        clear b1e4471
        have b1e4510 : (M.op (σ y) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e4472
             have i₂ := b1e312
             grind)
          | exact superpose b1e312 b1e4472
          | exact resolve b1e4472 b1e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e312 b1e4472
        have b1e4518 : (M.op (σ y) (σ y)) = (σ (k y x)) := by
          first
          | (have r₁ := b1e4510
             have r₂ := b1e3879
             grind)
          | exact resolve b1e4510 b1e3879
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3879 b1e4510
        have b1e5154 : (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e3880
             have i₂ := b1e4518
             grind)
          | exact superpose b1e4518 b1e3880
          | exact resolve b1e3880 b1e4518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3880
        have b1e5157 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e62 y y
             have i₂ := b1e4518
             grind)
          | exact superpose b1e4518 b1e62
          | exact resolve b1e62 b1e4518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62 b1e4518
        have b1e5189 : (σ (k y x)) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by grind
        clear b1e5157
        have b1e5211 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e5189
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e5189
          | exact resolve b1e5189 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e5189
        have b1e5212 : (σ y) = (σ (k y x)) := by grind
        clear b1e5211
        have b1e5222 : False := by grind
        exact b1e5222
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
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
        have b2e30 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 X1 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2 x
             have i₂ := b2e12 X0 X3 X2 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : y = (M.op y y) := by
          first
          | (have i₁ := b2e30 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e30
          | exact resolve b2e30 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e43 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b2e46 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (k X2 (M.op X0 X3)) = (M.op X2 X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e15 X2 (M.op X0 X3)
             have i₂ := b2e12 X0 X1 X2 X3
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X2 (M.op X0 X3)
             grind)
          | (have r₁ := b2e15 X2 (M.op X0 (M.op X1 X2))
             have r₂ := b2e12 X0 X1 X2 (M.op X1 X2)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e47 : (k x y) = (M.op x x) := by grind
        clear b2e43
        have b2e48 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b2e15 y y
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e15
          | (have r₁ := b2e15 y y
             have r₂ := b2e35
             grind)
          | exact resolve b2e15 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : y = (k y y) := by grind
        clear b2e48
        have b2e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e202 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 X1 x y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e33
          | exact resolve b2e33 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e204 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 X1 y y
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e33
          | exact resolve b2e33 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e276 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X2 x)) = (M.op X1 (M.op X0 y)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X0 (M.op X2 x) X3
             have i₂ := b2e202 X0 X2
             grind)
          | exact superpose b2e202 b2e12
          | exact resolve b2e12 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e299 : ∀ X1 X2 X3 : G, (M.op X1 y) = (M.op (M.op X1 X3) (M.op X2 x)) := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e276 x X1 X2 X3
             have i₂ := b2e204 X1 x
             grind)
          | exact superpose b2e204 b2e276
          | exact resolve b2e276 b2e204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e276
        have b2e309 : ∀ X1 X3 : G, (M.op X1 y) = (M.op (M.op X1 X3) y) := by
          intro X1 X3
          first
          | (have i₁ := b2e299 X1 x X3
             have i₂ := b2e202 (M.op X1 X3) x
             grind)
          | exact superpose b2e202 b2e299
          | exact resolve b2e299 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299
        have b2e2008 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
          intro X0 X1 X2
          first
          | (have j0 := b2e46 X1 X1 X0 (M.op X2 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e46
        have b2e2026 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X1 x)) = (k (M.op X1 x) (M.op X2 (M.op X0 y))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e2008 (M.op X1 x) X2 X0
             have i₂ := b2e202 X0 X1
             grind)
          | exact superpose b2e202 b2e2008
          | exact resolve b2e2008 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2049 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op (M.op X0 X1) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e2008 X2 X0 x
             have i₂ := b2e12 X0 x X2 X1
             grind)
          | exact superpose b2e12 b2e2008
          | exact resolve b2e2008 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2008
        have b2e2077 : ∀ X1 X2 : G, (M.op (M.op X1 x) (M.op X1 x)) = (k (M.op X1 x) (M.op X2 y)) := by
          intro X1 X2
          first
          | (have i₁ := b2e2026 x X1 X2
             have i₂ := b2e204 X2 x
             grind)
          | exact superpose b2e204 b2e2026
          | exact resolve b2e2026 b2e204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e204 b2e2026
        have b2e2078 : ∀ X1 X2 : G, (M.op (M.op X1 x) y) = (k (M.op X1 x) (M.op X2 y)) := by
          intro X1 X2
          first
          | (have i₁ := b2e2077 X1 X2
             have i₂ := b2e202 (M.op X1 x) X1
             grind)
          | exact superpose b2e202 b2e2077
          | exact resolve b2e2077 b2e202
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e202 b2e2077
        have b2e2079 : ∀ X1 X2 : G, (M.op X1 y) = (k (M.op X1 x) (M.op X2 y)) := by
          intro X1 X2
          first
          | (have i₁ := b2e2078 X1 X2
             have i₂ := b2e309 X1 x
             grind)
          | exact superpose b2e309 b2e2078
          | exact resolve b2e2078 b2e309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e309 b2e2078
        have b2e2080 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e63 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e63
        have b2e2081 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e2080
             have r₂ := b2e21
             grind)
          | exact resolve b2e2080 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2080
        have b2e2082 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2081
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2081
          | exact resolve b2e2081 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2081
        have b2e2083 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2082
             have i₂ := b2e47
             grind)
          | exact superpose b2e47 b2e2082
          | exact resolve b2e2082 b2e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e47 b2e2082
        have b2e2792 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e2083
             grind)
          | exact superpose b2e2083 b2e19
          | exact resolve b2e19 b2e2083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2794 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ (M.op x x)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (σ x) X0 X1 (σ y)
             have i₂ := b2e2083
             grind)
          | exact superpose b2e2083 b2e12
          | exact resolve b2e12 b2e2083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2808 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (σ (M.op x x))) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 X1 (σ y) (σ x)
             have i₂ := b2e2083
             grind)
          | exact superpose b2e2083 b2e33
          | exact resolve b2e33 b2e2083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2980 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e56 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e2981 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e2980 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2980
        have b2e3453 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b2e2079 X0 y
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e2079
          | exact resolve b2e2079 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e2079
        have b2e17765 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e2981 y
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e2981
          | (have j0 := b2e2981 y
             grind)
          | exact resolve b2e2981 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e2981
        have b2e17770 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e17765
        have b2e17784 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e2808 X0 (σ y)
             have i₂ := b2e17770
             grind)
          | exact superpose b2e17770 b2e2808
          | exact resolve b2e2808 b2e17770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e17801 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 X1 (σ y) (σ y)
             have i₂ := b2e17770
             grind)
          | exact superpose b2e17770 b2e33
          | exact resolve b2e33 b2e17770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e17850 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b2e2049 (σ y) (σ y) X0
             have i₂ := b2e17770
             grind)
          | exact superpose b2e17770 b2e2049
          | exact resolve b2e2049 b2e17770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2049
        have b2e17854 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b2e2794 (σ y) (σ y)
             have i₂ := b2e17770
             grind)
          | exact superpose b2e17770 b2e2794
          | exact resolve b2e2794 b2e17770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2794
        have b2e17857 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b2e17854
             have i₂ := b2e2083
             grind)
          | exact superpose b2e2083 b2e17854
          | exact resolve b2e17854 b2e2083
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2083 b2e17854
        have b2e23817 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (k (σ (M.op x x)) (M.op (σ y) (M.op X0 (σ y)))) := by
          intro X0
          first
          | (have i₁ := b2e17850 (σ (M.op x x))
             have i₂ := b2e2808 (σ y) X0
             grind)
          | exact superpose b2e2808 b2e17850
          | exact resolve b2e17850 b2e2808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2808 b2e17850
        have b2e23848 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (k (σ (M.op x x)) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b2e23817 x
             have i₂ := b2e17801 (σ y) x
             grind)
          | exact superpose b2e17801 b2e23817
          | exact resolve b2e23817 b2e17801
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17801 b2e23817
        have b2e23867 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (k (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b2e23848
             have i₂ := b2e17770
             grind)
          | exact superpose b2e17770 b2e23848
          | exact resolve b2e23848 b2e17770
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17770 b2e23848
        have b2e23877 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (k (M.op x x) y)) := by
          first
          | (have i₁ := b2e23867
             have i₂ := b2e18 (M.op x x) y
             grind)
          | exact superpose b2e18 b2e23867
          | exact resolve b2e23867 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23867
        have b2e23881 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
          first
          | (have i₁ := b2e23877
             have i₂ := b2e3453 x
             grind)
          | exact superpose b2e3453 b2e23877
          | exact resolve b2e23877 b2e3453
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3453 b2e23877
        have b2e23883 : (σ (M.op x y)) = (M.op (σ (M.op x x)) (σ y)) := by
          first
          | (have i₁ := b2e23881
             have i₂ := b2e17784 (σ (M.op x x))
             grind)
          | exact superpose b2e17784 b2e23881
          | exact resolve b2e23881 b2e17784
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17784 b2e23881
        have b2e35157 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e17857
             have i₂ := b2e23883
             grind)
          | exact superpose b2e23883 b2e17857
          | exact resolve b2e17857 b2e23883
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e17857 b2e23883
        have b2e35364 : False := by grind
        exact b2e35364
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
        have b3e28 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 (σ y) (σ x) X1
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e34 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 x X0 X1 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e40 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e34 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e34
          | exact resolve b3e34 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : (M.op y y) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b3e34 x y
             have i₂ := b3e40
             grind)
          | exact superpose b3e40 b3e34
          | exact resolve b3e34 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e60 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b3e57
             have i₂ := b3e34 y x
             grind)
          | exact superpose b3e34 b3e57
          | exact resolve b3e57 b3e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e34 b3e57
        have b3e72 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e20
          | exact resolve b3e20 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e171 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e28 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e28
          | exact resolve b3e28 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e194 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e171
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e171
          | exact resolve b3e171 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e171
        have b3e206 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e194
             grind)
          | exact superpose b3e194 b3e15
          | (have r₁ := b3e15 (σ y) (σ y)
             have r₂ := b3e194
             grind)
          | exact resolve b3e15 b3e194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e194
        have b3e210 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e206
        have b3e211 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e210
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e210
          | exact resolve b3e210 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210
        have b3e321 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e211
             grind)
          | exact superpose b3e211 b3e13
          | exact resolve b3e13 b3e211
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e211
        have b3e323 : y = (k y y) := by
          first
          | (have i₁ := b3e321
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e321
          | exact resolve b3e321 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e321
        have b3e363 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e323
             grind)
          | exact superpose b3e323 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e323
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e323
        have b3e364 : y = (M.op y y) := by grind
        clear b3e363
        have b3e366 : False := by grind
        exact b3e366
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
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
          have b4e39 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ x) X0 X1 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X0 X1 X2 x
               have i₂ := b4e13 X0 X3 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e40 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40
            | exact resolve b4e40 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : (M.op x y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e40 y x
               have i₂ := b4e46
               grind)
            | exact superpose b4e46 b4e40
            | exact resolve b4e40 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e66 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e63
               have i₂ := b4e40 x y
               grind)
            | exact superpose b4e40 b4e63
            | exact resolve b4e63 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e63
          have b4e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b4e120 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e34 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e317 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b4e34 (σ x) (M.op x X0)
               have i₂ := b4e39 x X0
               grind)
            | exact superpose b4e39 b4e34
            | exact resolve b4e34 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e324 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e317 x
               have i₂ := b4e34 (σ y) x
               grind)
            | exact superpose b4e34 b4e317
            | exact resolve b4e317 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e317
          have b4e415 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e572 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X2) x) := by
            intro X0 X2
            first
            | (have i₁ := b4e13 X0 x x X2
               have i₂ := b4e415 X0 x
               grind)
            | exact superpose b4e415 b4e13
            | exact resolve b4e13 b4e415
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e415
          have b4e4064 : (σ y) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e120
               grind)
            | exact superpose b4e120 b4e23
            | exact resolve b4e23 b4e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120
          have b4e7474 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e73 y y
               have i₂ := b4e324
               grind)
            | exact superpose b4e324 b4e73
            | exact resolve b4e73 b4e324
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e324
          have b4e7512 : (M.op (σ x) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b4e7474
          have b4e7528 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have r₁ := b4e7512
               have r₂ := b4e4064
               grind)
            | exact resolve b4e7512 b4e4064
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4064 b4e7512
          have b4e7545 : (σ (M.op x y)) ≠ (σ (k y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e7528
               grind)
            | exact superpose b4e7528 b4e20
            | exact resolve b4e20 b4e7528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7528
          have b4e10872 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e7545
               have i₂ := b4e18 y y
               grind)
            | exact superpose b4e18 b4e7545
            | (have j1 := b4e18 y y
               grind)
            | exact resolve b4e7545 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7545
          have b4e10873 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e10872
          have b4e10874 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b4e10873
               have i₂ := b4e66
               grind)
            | exact superpose b4e66 b4e10873
            | exact resolve b4e10873 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e10873
          have b4e10875 : y = (M.op y y) := by grind
          clear b4e10874
          have b4e11920 : y = (M.op y x) := by
            first
            | (have i₁ := b4e572 y y
               have i₂ := b4e10875
               grind)
            | exact superpose b4e10875 b4e572
            | exact resolve b4e572 b4e10875
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572 b4e10875
          have b4e11928 : False := by grind
          exact b4e11928
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e36 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2 x
               have i₂ := b5e13 X0 X3 X2 x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e36 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e36
            | exact resolve b5e36 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e58 : (M.op x y) = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b5e36 y x
               have i₂ := b5e41
               grind)
            | exact superpose b5e41 b5e36
            | exact resolve b5e36 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e61 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b5e58
               have i₂ := b5e36 x y
               grind)
            | exact superpose b5e36 b5e58
            | exact resolve b5e58 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e58
          have b5e75 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e79 : y = (k x y) ∨ y = (M.op y x) := by grind
          have b5e82 : y = (k x y) := by
            first
            | (have r₁ := b5e79
               have r₂ := b5e21
               grind)
            | exact resolve b5e79 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e239 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e39 X0 X1 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39
            | exact resolve b5e39 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39
          have b5e531 : ∀ X0 X2 : G, (M.op X0 y) = (M.op (M.op X0 X2) x) := by
            intro X0 X2
            first
            | (have i₁ := b5e13 X0 x x X2
               have i₂ := b5e239 X0 x
               grind)
            | exact superpose b5e239 b5e13
            | exact resolve b5e13 b5e239
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e239
          have b5e2332 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e75 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e2333 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2332
               have r₂ := b5e23
               grind)
            | exact resolve b5e2332 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2332
          have b5e2334 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2333
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2333
            | exact resolve b5e2333 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2333
          have b5e2335 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e2334
               have i₂ := b5e82
               grind)
            | exact superpose b5e82 b5e2334
            | exact resolve b5e2334 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e2334
          have b5e2336 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e2335
               grind)
            | exact superpose b5e2335 b5e20
            | exact resolve b5e20 b5e2335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2337 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (σ x) (σ y) X1
               have i₂ := b5e2335
               grind)
            | exact superpose b5e2335 b5e13
            | exact resolve b5e13 b5e2335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7714 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e2337 (σ x) (σ y)
               have i₂ := b5e2335
               grind)
            | exact superpose b5e2335 b5e2337
            | exact resolve b5e2337 b5e2335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2335 b5e2337
          have b5e8531 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b5e16 (σ y) (σ y)
               have i₂ := b5e7714
               grind)
            | exact superpose b5e7714 b5e16
            | (have r₁ := b5e16 (σ y) (σ y)
               have r₂ := b5e7714
               grind)
            | exact resolve b5e16 b5e7714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7714
          have b5e8565 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b5e8531
          have b5e8573 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e8565
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e8565
            | exact resolve b5e8565 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8565
          have b5e8815 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e8573
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e8573
            | (have j1 := b5e18 y y
               grind)
            | exact resolve b5e8573 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8573
          have b5e8826 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b5e8815
          have b5e8835 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e8826
               have i₂ := b5e61
               grind)
            | exact superpose b5e61 b5e8826
            | exact resolve b5e8826 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61 b5e8826
          have b5e8839 : y = (M.op y y) := by
            first
            | (have r₁ := b5e8835
               have r₂ := b5e2336
               grind)
            | exact resolve b5e8835 b5e2336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2336 b5e8835
          have b5e9694 : y = (M.op y x) := by
            first
            | (have i₁ := b5e531 y y
               have i₂ := b5e8839
               grind)
            | exact superpose b5e8839 b5e531
            | exact resolve b5e531 b5e8839
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e531 b5e8839
          have b5e9700 : False := by grind
          exact b5e9700
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ x)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 (σ y) (σ x) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 X1 X2 x
             have i₂ := b6e12 X0 X3 X2 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e43 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e40
        have b6e44 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e43
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e43
          | exact resolve b6e43 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e67 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b6e15 (σ x) (σ x)
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e15
          | exact resolve b6e15 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e71 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b6e67
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e67
          | exact resolve b6e67 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e88 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e26 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e26
          | exact resolve b6e26 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e104 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e88
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e88
          | exact resolve b6e88 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e109 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e104
             grind)
          | exact superpose b6e104 b6e15
          | (have r₁ := b6e15 (σ y) (σ y)
             have r₂ := b6e104
             grind)
          | exact resolve b6e15 b6e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e104
        have b6e112 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b6e109
        have b6e113 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e112
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e112
          | exact resolve b6e112 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e112
        have b6e187 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e113
             grind)
          | exact superpose b6e113 b6e13
          | exact resolve b6e13 b6e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113
        have b6e189 : y = (k y y) := by
          first
          | (have i₁ := b6e187
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e187
          | exact resolve b6e187 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e187
        have b6e218 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e189
             grind)
          | exact superpose b6e189 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e189
        have b6e219 : y = (M.op y y) := by grind
        clear b6e218
        have b6e320 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 y X0 X1 y
             have i₂ := b6e219
             grind)
          | exact superpose b6e219 b6e12
          | exact resolve b6e12 b6e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e326 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b6e34 X0 X1 y y
             have i₂ := b6e219
             grind)
          | exact superpose b6e219 b6e34
          | exact resolve b6e34 b6e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e3591 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e57 x x
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e57
          | exact resolve b6e57 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e57
        have b6e3724 : (σ x) = (σ (k x y)) ∨ (σ (k x y)) = (σ (k x x)) := by grind
        clear b6e3591
        have b6e3754 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have r₁ := b6e3724
             have r₂ := b6e71
             grind)
          | exact resolve b6e3724 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71 b6e3724
        have b6e3785 : (k x x) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3754
             grind)
          | exact superpose b6e3754 b6e13
          | exact resolve b6e13 b6e3754
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3754
        have b6e3805 : (k x y) = (k x x) := by
          first
          | (have i₁ := b6e3785
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e3785
          | exact resolve b6e3785 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3785
        have b6e3864 : (M.op x x) = (k x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e3805
             grind)
          | exact superpose b6e3805 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e3805
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e3865 : (M.op x x) = (k x y) ∨ x = (M.op x x) := by grind
        clear b6e3864
        have b6e13361 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e3865
             grind)
          | exact superpose b6e3865 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e3865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3865
        have b6e13362 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b6e13361
             have r₂ := b6e21
             grind)
          | exact resolve b6e13361 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13361
        have b6e13370 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b6e13362
             have r₂ := b6e20
             grind)
          | exact resolve b6e13362 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13362
        have b6e15799 : (M.op y x) = (M.op y (M.op x y)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e320 x x
             have i₂ := b6e13370
             grind)
          | exact superpose b6e13370 b6e320
          | exact resolve b6e320 b6e13370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13370
        have b6e15815 : (M.op y x) = (M.op y y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e15799
             have i₂ := b6e326 y x
             grind)
          | exact superpose b6e326 b6e15799
          | exact resolve b6e15799 b6e326
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e326 b6e15799
        have b6e15837 : y = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e15815
             have i₂ := b6e219
             grind)
          | exact superpose b6e219 b6e15815
          | exact resolve b6e15815 b6e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15815
        have b6e15852 : x = (M.op x x) := by
          first
          | (have r₁ := b6e15837
             have r₂ := b6e20
             grind)
          | exact resolve b6e15837 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15837
        have b6e16651 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b6e15 x x
             have i₂ := b6e15852
             grind)
          | exact superpose b6e15852 b6e15
          | (have r₁ := b6e15 x x
             have r₂ := b6e15852
             grind)
          | exact resolve b6e15 b6e15852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15852
        have b6e16692 : x = (k x x) := by grind
        clear b6e16651
        have b6e17065 : x = (k x y) := by
          first
          | (have i₁ := b6e3805
             have i₂ := b6e16692
             grind)
          | exact superpose b6e16692 b6e3805
          | exact resolve b6e3805 b6e16692
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3805 b6e16692
        have b6e17132 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e17065
             grind)
          | exact superpose b6e17065 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e17065
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17065
        have b6e17135 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e17132
             have r₂ := b6e21
             grind)
          | exact resolve b6e17132 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17132
        have b6e17140 : x = (M.op x y) := by
          first
          | (have r₁ := b6e17135
             have r₂ := b6e20
             grind)
          | exact resolve b6e17135 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17135
        have b6e17206 : (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e320 x y
             have i₂ := b6e17140
             grind)
          | exact superpose b6e17140 b6e320
          | exact resolve b6e320 b6e17140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e320 b6e17140
        have b6e17225 : y = (M.op y x) := by
          first
          | (have i₁ := b6e17206
             have i₂ := b6e219
             grind)
          | exact superpose b6e219 b6e17206
          | exact resolve b6e17206 b6e219
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e219 b6e17206
        have b6e17247 : False := by grind
        exact b6e17247
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
          have b7e50 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e53 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e50
            | exact resolve b7e50 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e3852 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e67 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e67
            | exact resolve b7e67 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e3979 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
          clear b7e3852
          have b7e4007 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e3979
               have r₂ := b7e53
               grind)
            | exact resolve b7e3979 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53 b7e3979
          have b7e4038 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e4007
               grind)
            | exact superpose b7e4007 b7e14
            | exact resolve b7e14 b7e4007
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4007
          have b7e4056 : y = (k x x) := by
            first
            | (have i₁ := b7e4038
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e4038
            | exact resolve b7e4038 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4038
          have b7e4108 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e4056
               grind)
            | exact superpose b7e4056 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e4056
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4109 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e4108
          have b7e4111 : x = (M.op x x) := by
            first
            | (have r₁ := b7e4109
               have r₂ := b7e22
               grind)
            | exact resolve b7e4109 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4109
          have b7e4698 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e4111
               grind)
            | exact superpose b7e4111 b7e22
            | exact resolve b7e22 b7e4111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e4702 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b7e16 x x
               have i₂ := b7e4111
               grind)
            | exact superpose b7e4111 b7e16
            | (have r₁ := b7e16 x x
               have r₂ := b7e4111
               grind)
            | exact resolve b7e16 b7e4111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4111
          have b7e4725 : x = (k x x) := by grind
          clear b7e4702
          have b7e5549 : x = y := by
            first
            | (have i₁ := b7e4056
               have i₂ := b7e4725
               grind)
            | exact superpose b7e4725 b7e4056
            | exact resolve b7e4056 b7e4725
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4056 b7e4725
          have b7e5561 : False := by grind
          exact b7e5561
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
          have b8e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e1802 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e71 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e1803 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1802
               have r₂ := b8e23
               grind)
            | exact resolve b8e1802 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1802
          have b8e1804 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1803
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1803
            | exact resolve b8e1803 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1803
          have b8e1805 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1804
               grind)
            | exact superpose b8e1804 b8e20
            | exact resolve b8e20 b8e1804
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1804
          have b8e1884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1805
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1805
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1805 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1805
          have b8e1885 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e1884
          have b8e1887 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1885
               have r₂ := b8e22
               grind)
            | exact resolve b8e1885 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1885
          have b8e1889 : False := by grind
          exact b8e1889
