import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2670`: `x = ((x ◇ y) ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation2670 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2670 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2670.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e61 : False := by grind
      exact b0e61
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
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b5e46 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e49 : x = y ∨ x = (k x y) := by grind
          clear b5e46
          have b5e50 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e158 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e878 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e158 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e158
            | (have j0 := b5e158 x y
               grind)
            | exact resolve b5e158 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e158
          have b5e882 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e878
          have b5e885 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e882
               have r₂ := b5e24
               grind)
            | exact resolve b5e882 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e882
          have b5e889 : False := by grind
          exact b5e889
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e122 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e133 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e122
               have r₂ := b8e24
               grind)
            | exact resolve b8e122 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e138 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e133
               have r₂ := b8e23
               grind)
            | exact resolve b8e133 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e141 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e138
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e138
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e138
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e138
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e138 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138
          have b8e142 : x = (M.op x y) ∨ x = y := by grind
          clear b8e141
          have b8e143 : x = y := by
            first
            | (have r₁ := b8e142
               have r₂ := b8e22
               grind)
            | exact resolve b8e142 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142
          have b8e144 : False := by grind
          exact b8e144

/-- `Equation2700`: `x = ((y ◇ x) ◇ (x ◇ y)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation2700 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2700 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2700.models_iff G M).mp hM
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
      have b0e176 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e56 x
           grind)
        | exact superpose b0e56 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e56 x
           grind)
        | exact resolve b0e22 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e56
      have b0e185 : False := by grind
      exact b0e185
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
        have b1e53 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
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
        have b1e56 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e53
        have b1e57 : (k x y) = (M.op y y) := by grind
        clear b1e52
        have b1e58 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e56
          | exact resolve b1e56 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e55 y
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
        have b1e133 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
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
        have b1e765 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e77 (σ x)
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e77
          | (have j0 := b1e77 (σ x)
             grind)
          | (have r₁ := b1e77 (σ x)
             have r₂ := b1e59
             grind)
          | exact resolve b1e77 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e77
        have b1e768 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e765
        have b1e771 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e768
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e768
          | exact resolve b1e768 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e768
        have b1e775 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e771
             have r₂ := b1e133
             grind)
          | exact resolve b1e771 b1e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e771
        have b1e779 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e775
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e775
          | exact resolve b1e775 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e775
        have b1e781 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e779
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e779
          | exact resolve b1e779 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e779
        have b1e783 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e781
             have i₂ := b1e68 x
             grind)
          | exact superpose b1e68 b1e781
          | exact resolve b1e781 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68 b1e781
        have b1e785 : False := by grind
        exact b1e785
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
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (k x y) = (M.op y y) := by grind
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
             have i₂ := b2e61 y
             grind)
          | exact superpose b2e61 b2e22
          | exact resolve b2e22 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1402 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e95 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e1403 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1402
             have r₂ := b2e21
             grind)
          | exact resolve b2e1402 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1402
        have b2e1409 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1403
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1403
          | exact resolve b2e1403 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1403
        have b2e1413 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1409
             have i₂ := b2e52
             grind)
          | exact superpose b2e52 b2e1409
          | exact resolve b2e1409 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e1409
        have b2e1414 : False := by grind
        exact b2e1414
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
        have b3e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e53
        have b3e58 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
             have i₂ := b3e58
             grind)
          | exact superpose b3e58 b3e15
          | exact resolve b3e15 b3e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
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
             have i₂ := b3e55 y
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
        have b3e198 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e68 x
             grind)
          | exact superpose b3e68 b3e23
          | exact resolve b3e23 b3e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e68
        have b3e354 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e75 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e355 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e354
             have r₂ := b3e20
             grind)
          | exact resolve b3e354 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e354
        have b3e359 : (σ (M.op x y)) = (σ (M.op x x)) := by
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
          have b4e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e66
          have b4e72 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e70
            | exact resolve b4e70 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e69 y
               grind)
            | exact superpose b4e69 b4e72
            | exact resolve b4e72 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69 b4e72
          have b4e75 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e74
            | exact resolve b4e74 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e76 : False := by grind
          exact b4e76
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
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b5e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e69 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e69
            | exact resolve b5e69 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e69
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
          have b5e341 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e87 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e342 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e341
               have r₂ := b5e21
               grind)
            | exact resolve b5e341 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e341
          have b5e1587 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e1588 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1587
               have r₂ := b5e23
               grind)
            | exact resolve b5e1587 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1587
          have b5e1595 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1588
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1588
            | exact resolve b5e1588 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1588
          have b5e1602 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1595
               have i₂ := b5e342
               grind)
            | exact superpose b5e342 b5e1595
            | exact resolve b5e1595 b5e342
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e342 b5e1595
          have b5e1613 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1602
               grind)
            | exact superpose b5e1602 b5e23
            | exact resolve b5e23 b5e1602
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1602
          have b5e1639 : False := by grind
          exact b5e1639
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
        have b6e50 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e50
        have b6e53 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e72 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e53
             grind)
          | exact superpose b6e53 b6e15
          | exact resolve b6e15 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
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
             have i₂ := b6e51 y
             grind)
          | exact superpose b6e51 b6e78
          | exact resolve b6e78 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e78
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
        have b6e156 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
        have b6e157 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e156
        have b6e159 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e157
             have r₂ := b6e21
             grind)
          | exact resolve b6e157 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e161 : False := by grind
        exact b6e161
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
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e63
          have b7e67 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e68 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e65 y
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e70
            | exact resolve b7e70 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e70
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
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e88
            | (have j0 := b7e88 X0
               grind)
            | exact resolve b7e88 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e91 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e23
            | exact resolve b7e23 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e97 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e91
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e91
            | exact resolve b7e91 b7e79
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
          have b7e681 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e90 (σ x)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e90
            | (have j0 := b7e90 (σ x)
               grind)
            | (have r₁ := b7e90 (σ x)
               have r₂ := b7e68
               grind)
            | exact resolve b7e90 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e90
          have b7e684 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e681
          have b7e687 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e684
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e684
            | exact resolve b7e684 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e684
          have b7e691 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e687
               have r₂ := b7e97
               grind)
            | exact resolve b7e687 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e687
          have b7e695 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e691
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e691
            | exact resolve b7e691 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e691
          have b7e697 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e695
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e695
            | exact resolve b7e695 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e695
          have b7e703 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e697
               have i₂ := b7e137 x y
               grind)
            | exact superpose b7e137 b7e697
            | (have j1 := b7e137 x y
               grind)
            | exact resolve b7e697 b7e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e137
          have b7e705 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e697
               grind)
            | exact superpose b7e697 b7e14
            | exact resolve b7e14 b7e697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e697
          have b7e717 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e705
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e705
            | exact resolve b7e705 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e705
          have b7e719 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e703
               have r₂ := b7e97
               grind)
            | exact resolve b7e703 b7e97
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97 b7e703
          have b7e722 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e719
               have r₂ := b7e22
               grind)
            | exact resolve b7e719 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e719
          have b7e723 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e722
               have i₂ := b7e717
               grind)
            | exact superpose b7e717 b7e722
            | exact resolve b7e722 b7e717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e717 b7e722
          have b7e724 : False := by grind
          exact b7e724
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
          have b8e1356 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e123 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e1357 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1356
               have r₂ := b8e23
               grind)
            | exact resolve b8e1356 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1356
          have b8e1363 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1357
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1357
            | exact resolve b8e1357 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1357
          have b8e1374 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1363
               grind)
            | exact superpose b8e1363 b8e20
            | exact resolve b8e20 b8e1363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1363
          have b8e1474 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1374
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1374
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1374 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1374
          have b8e1475 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1474
          have b8e1477 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1475
               have r₂ := b8e21
               grind)
            | exact resolve b8e1475 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1475
          have b8e1480 : False := by grind
          exact b8e1480

/-- `Equation2910`: `x = ((y ◇ (x ◇ y)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation2910 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2910 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2910.models_iff G M).mp hM
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
      have b0e186 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
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
      have b0e196 : False := by grind
      exact b0e196
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
        have b1e50 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        clear b1e50
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
        have b1e620 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e621 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e620
        have b1e622 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e621
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e621
          | exact resolve b1e621 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e621
        have b1e624 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e622
             have r₂ := b1e124
             grind)
          | exact resolve b1e622 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e622
        have b1e626 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e624
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e624
          | exact resolve b1e624 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e624
        have b1e627 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e626
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e626
          | exact resolve b1e626 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e626
        have b1e628 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e627
             have i₂ := b1e65 x
             grind)
          | exact superpose b1e65 b1e627
          | exact resolve b1e627 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e627
        have b1e629 : False := by grind
        exact b1e629
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
        have b2e134 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
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
        have b2e977 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e978 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e977
             have r₂ := b2e21
             grind)
          | exact resolve b2e977 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e977
        have b2e981 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e978
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e978
          | exact resolve b2e978 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e978
        have b2e983 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e981
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e981
          | exact resolve b2e981 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e981
        have b2e984 : False := by grind
        exact b2e984
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
        have b3e182 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
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
        have b3e231 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
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
        have b3e236 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e232
             grind)
          | exact superpose b3e232 b3e81
          | exact resolve b3e81 b3e232
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e232
        have b3e240 : False := by grind
        exact b3e240
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
          have b4e63 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b4e63
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
          have b5e1218 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1219 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1218
               have r₂ := b5e23
               grind)
            | exact resolve b5e1218 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1218
          have b5e1223 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1219
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1219
            | exact resolve b5e1219 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1219
          have b5e1227 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1223
               have i₂ := b5e257
               grind)
            | exact superpose b5e257 b5e1223
            | exact resolve b5e1223 b5e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e257 b5e1223
          have b5e1233 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1227
               grind)
            | exact superpose b5e1227 b5e23
            | exact resolve b5e23 b5e1227
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1227
          have b5e1244 : False := by grind
          exact b5e1244
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
          have b7e61 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b7e61
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
          have b7e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
            | (have j0 := b7e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e606 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e607 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e606
          have b7e608 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e607
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e607
            | exact resolve b7e607 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e607
          have b7e610 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e608
               have r₂ := b7e94
               grind)
            | exact resolve b7e608 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e608
          have b7e612 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e610
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e610
            | exact resolve b7e610 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e610
          have b7e613 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e612
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e612
            | exact resolve b7e612 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e612
          have b7e615 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e613
               have i₂ := b7e128 x y
               grind)
            | exact superpose b7e128 b7e613
            | (have j1 := b7e128 x y
               grind)
            | exact resolve b7e613 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e617 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e613
               grind)
            | exact superpose b7e613 b7e14
            | exact resolve b7e14 b7e613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e613
          have b7e636 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e617
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e617
            | exact resolve b7e617 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617
          have b7e638 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e615
               have r₂ := b7e94
               grind)
            | exact resolve b7e615 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e615
          have b7e641 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e638
               have r₂ := b7e22
               grind)
            | exact resolve b7e638 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e638
          have b7e642 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e641
               have i₂ := b7e636
               grind)
            | exact superpose b7e636 b7e641
            | exact resolve b7e641 b7e636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e636 b7e641
          have b7e643 : False := by grind
          exact b7e643
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
          have b8e1023 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1024 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1023
               have r₂ := b8e23
               grind)
            | exact resolve b8e1023 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1023
          have b8e1027 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1024
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1024
            | exact resolve b8e1024 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1024
          have b8e1034 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1027
               grind)
            | exact superpose b8e1027 b8e20
            | exact resolve b8e20 b8e1027
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1027
          have b8e1102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1034
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1034
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1034 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1034
          have b8e1103 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1102
          have b8e1105 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1103
               have r₂ := b8e21
               grind)
            | exact resolve b8e1103 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1103
          have b8e1108 : False := by grind
          exact b8e1108

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3352 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
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
        have b1e45 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        clear b1e45
        have b1e48 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e23
             grind)
          | exact resolve b1e47 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ y) = (σ (k x y)) := by
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
        have b1e50 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e49
          | exact resolve b1e49 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e49
        have b1e51 : False := by grind
        exact b1e51
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
        have b2e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e117 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e460 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e117 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e117
          | (have j0 := b2e117 x y
             grind)
          | exact resolve b2e117 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e117
        have b2e464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e460
        have b2e467 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e464
             have r₂ := b2e22
             grind)
          | exact resolve b2e464 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e464
        have b2e471 : False := by grind
        exact b2e471
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
        have b3e40 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e42 : x = y ∨ y = (k x y) := by grind
        clear b3e40
        have b3e43 : y = (k x y) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e23
             grind)
          | exact resolve b3e42 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e42
        have b3e46 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e29
          | exact resolve b3e29 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e43
        have b3e47 : False := by grind
        exact b3e47
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
          have b5e44 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e46 : x = y ∨ y = (k x y) := by grind
          clear b5e44
          have b5e47 : y = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e25
               grind)
            | exact resolve b5e46 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e46
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e108 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e420 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e108 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e108
            | (have j0 := b5e108 x y
               grind)
            | exact resolve b5e108 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e108
          have b5e423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e420
          have b5e426 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e423
               have r₂ := b5e24
               grind)
            | exact resolve b5e423 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e423
          have b5e430 : False := by grind
          exact b5e430
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
        have b6e46 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e48 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e46
        have b6e51 : y = (M.op x y) := by
          first
          | (have r₁ := b6e48
             have r₂ := b6e21
             grind)
          | exact resolve b6e48 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48
        have b6e54 : False := by grind
        exact b6e54
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
          have b7e36 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e25
               grind)
            | exact resolve b7e38 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e38
          have b7e40 : (σ y) = (σ (k x y)) := by
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
          have b7e43 : (k x y) = (τ (σ y)) := by
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
          have b7e44 : y = (k x y) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e43
            | exact resolve b7e43 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
          have b7e55 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e54
          have b7e57 : x = (M.op x y) := by
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
          have b8e90 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e103 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e90
               have r₂ := b8e24
               grind)
            | exact resolve b8e90 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e106 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e103
               have r₂ := b8e23
               grind)
            | exact resolve b8e103 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e106
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e106
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e106 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e108 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e107
          have b8e109 : y = (M.op x y) := by
            first
            | (have r₁ := b8e108
               have r₂ := b8e22
               grind)
            | exact resolve b8e108 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e110 : False := by grind
          exact b8e110

/-- `Equation3961`: `x ◇ y = (y ◇ (y ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pyx_pyx_pxy_Equation3961 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3961 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3961.models_iff G M).mp hM
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
      have b0e73 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        grind
      have b0e74 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
        intro X0
        first
        | (have j0 := b0e73 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e92 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have i₁ := b0e74 (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e74
        | exact resolve b0e74 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93 : (M.op x y) = (k y x) := by
        first
        | (have i₁ := b0e74 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e74
        | exact resolve b0e74 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74
      have b0e96 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e92
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e92
        | exact resolve b0e92 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92
      have b0e97 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e96
           have i₂ := b0e93
           grind)
        | exact superpose b0e93 b0e96
        | exact resolve b0e96 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93 b0e96
      have b0e98 : False := by grind
      exact b0e98
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
        have b1e32 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e33 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e32
          | exact resolve b1e32 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e67 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b1e68 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b1e67 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67
        have b1e83 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e33
             grind)
          | exact superpose b1e33 b1e19
          | exact resolve b1e19 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e119 : (M.op x y) = (k y x) := by
          first
          | (have i₁ := b1e68 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e68
          | exact resolve b1e68 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e125 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e83
             have i₂ := b1e119
             grind)
          | exact superpose b1e119 b1e83
          | exact resolve b1e83 b1e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83 b1e119
        have b1e127 : False := by grind
        exact b1e127
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e42 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b2e61 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e62 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e61 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e321 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e62 X0
             have i₂ := b2e42 X0 X1
             grind)
          | (have i₁ := b2e62 X0
             have i₂ := b2e42 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e42 b2e62
          | (have j1 := b2e42 X1 X0
             grind)
          | exact resolve b2e62 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e62
        have b2e338 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e321 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e321
        have b2e547 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e338 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e338
        have b2e548 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e547 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e547
        have b2e642 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e548 (σ X0)
             grind)
          | exact superpose b2e548 b2e18
          | exact resolve b2e18 b2e548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e650 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e642 X0
             have i₂ := b2e548 X0
             grind)
          | exact superpose b2e548 b2e642
          | exact resolve b2e642 b2e548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e642
        have b2e725 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e45 x x
             grind)
          | exact superpose b2e45 b2e21
          | (have j1 := b2e45 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e45 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e45 y x
             grind)
          | exact resolve b2e21 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e815 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e725
        have b2e885 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e815
             have i₂ := b2e548 x
             grind)
          | exact superpose b2e548 b2e815
          | exact resolve b2e815 b2e548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e548 b2e815
        have b2e971 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e885
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e885
          | exact resolve b2e885 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e885
        have b2e972 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e971
        have b2e1018 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e972
             have i₂ := b2e650 x
             grind)
          | exact superpose b2e650 b2e972
          | exact resolve b2e972 b2e650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e972
        have b2e1038 : (σ x) = (σ y) := by
          first
          | (have i₁ := b2e1018
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1018
          | exact resolve b2e1018 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1018
        have b2e1082 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1038
             grind)
          | exact superpose b2e1038 b2e22
          | exact resolve b2e22 b2e1038
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1107 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1082
             have i₂ := b2e650 x
             grind)
          | exact superpose b2e650 b2e1082
          | exact resolve b2e1082 b2e650
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e650 b2e1082
        have b2e1115 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e1107
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1107
          | exact resolve b2e1107 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1107
        have b2e1123 : False := by grind
        exact b2e1123
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
        have b3e31 : (M.op x y) = (k y x) := by grind
        have b3e58 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b3e70 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e58
          | exact resolve b3e58 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e71 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e70
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e70
          | exact resolve b3e70 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70
        have b3e72 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b3e71
             have r₂ := b3e19
             grind)
          | exact resolve b3e71 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e81 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        clear b3e72
        have b3e82 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e81
          | exact resolve b3e81 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e84 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e31
             grind)
          | exact superpose b3e31 b3e82
          | exact resolve b3e82 b3e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31 b3e82
        have b3e86 : False := by grind
        exact b3e86
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
          have b4e37 : (M.op x y) = (k y x) := by grind
          have b4e38 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e40 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e38
            | exact resolve b4e38 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e41 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e40
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e40
            | exact resolve b4e40 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e40
          have b4e42 : False := by grind
          exact b4e42
        · have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b5e72 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e73 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e72 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e72
          have b5e317 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e73 X0
               have i₂ := b5e49 X0 X1
               grind)
            | (have i₁ := b5e73 X0
               have i₂ := b5e49 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e49 b5e73
            | (have j1 := b5e49 X1 X0
               grind)
            | exact resolve b5e73 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e73
          have b5e332 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e317 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e317
          have b5e534 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e332 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e332
          have b5e535 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e534 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e534
          have b5e623 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e535 (σ X0)
               grind)
            | exact superpose b5e535 b5e19
            | exact resolve b5e19 b5e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e631 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e623 X0
               have i₂ := b5e535 X0
               grind)
            | exact superpose b5e535 b5e623
            | exact resolve b5e623 b5e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e623
          have b5e707 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e52 y y
               grind)
            | exact superpose b5e52 b5e24
            | (have j1 := b5e52 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e52 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e52 x y
               grind)
            | exact resolve b5e24 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e795 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e707
          have b5e865 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e795
               have i₂ := b5e535 y
               grind)
            | exact superpose b5e535 b5e795
            | exact resolve b5e795 b5e535
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e535 b5e795
          have b5e951 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e865
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e865
            | exact resolve b5e865 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e865
          have b5e952 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e951
          have b5e999 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e952
               have i₂ := b5e631 y
               grind)
            | exact superpose b5e631 b5e952
            | exact resolve b5e952 b5e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e952
          have b5e1019 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e999
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e999
            | exact resolve b5e999 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e999
          have b5e1062 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1019
               grind)
            | exact superpose b5e1019 b5e20
            | exact resolve b5e20 b5e1019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1068 : y = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e1019
               grind)
            | exact superpose b5e1019 b5e14
            | exact resolve b5e14 b5e1019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1019
          have b5e1085 : x = y := by
            first
            | (have i₁ := b5e1068
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1068
            | exact resolve b5e1068 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1068
          have b5e1089 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1062
               have i₂ := b5e631 x
               grind)
            | exact superpose b5e631 b5e1062
            | exact resolve b5e1062 b5e631
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e631 b5e1062
          have b5e1094 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1089
               have i₂ := b5e1085
               grind)
            | exact superpose b5e1085 b5e1089
            | exact resolve b5e1089 b5e1085
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1085 b5e1089
          have b5e1095 : False := by grind
          exact b5e1095
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
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e69 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e70 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e69 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e409 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e70 X0
             have i₂ := b6e55 X0 X1
             grind)
          | (have i₁ := b6e70 X0
             have i₂ := b6e55 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e55 b6e70
          | (have j1 := b6e55 X1 X0
             grind)
          | exact resolve b6e70 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e70
        have b6e425 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e409 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e409
        have b6e624 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e425 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e425
        have b6e625 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e624 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e624
        have b6e719 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e625 (σ X0)
             grind)
          | exact superpose b6e625 b6e18
          | exact resolve b6e18 b6e625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e726 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e719 X0
             have i₂ := b6e625 X0
             grind)
          | exact superpose b6e625 b6e719
          | exact resolve b6e719 b6e625
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e625 b6e719
        have b6e1447 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e726 x
             grind)
          | exact superpose b6e726 b6e22
          | exact resolve b6e22 b6e726
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e726
        have b6e1683 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e1447
             grind)
          | exact superpose b6e1447 b6e13
          | exact resolve b6e13 b6e1447
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1447
        have b6e1702 : y = (M.op x x) := by
          first
          | (have i₁ := b6e1683
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1683
          | exact resolve b6e1683 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1683
        have b6e1707 : False := by grind
        exact b6e1707
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
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e77 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e78 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e77 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e233 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e78 X0
               have i₂ := b7e56 X0 X1
               grind)
            | (have i₁ := b7e78 X0
               have i₂ := b7e56 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e56 b7e78
            | (have j1 := b7e56 X1 X0
               grind)
            | exact resolve b7e78 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56 b7e78
          have b7e246 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e233 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233
          have b7e274 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e246 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e246
          have b7e297 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e274 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e274
            | exact resolve b7e274 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e308 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e274 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e274
          have b7e314 : (σ x) = (k (σ y) (σ y)) := by grind
          clear b7e297
          have b7e326 : (σ x) = (σ (k y y)) := by
            first
            | (have i₁ := b7e314
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e314
            | exact resolve b7e314 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e314
          have b7e339 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e326
               have i₂ := b7e308 y
               grind)
            | exact superpose b7e308 b7e326
            | exact resolve b7e326 b7e308
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e308 b7e326
          have b7e470 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e339
               grind)
            | exact superpose b7e339 b7e14
            | exact resolve b7e14 b7e339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e339
          have b7e471 : x = (M.op y y) := by
            first
            | (have i₁ := b7e470
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e470
            | exact resolve b7e470 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e470
          have b7e476 : False := by grind
          exact b7e476
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
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
          have b8e321 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e322 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e321
               have r₂ := b8e24
               grind)
            | exact resolve b8e321 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e321
          have b8e323 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e322
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e322
            | exact resolve b8e322 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e322
          have b8e324 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e323
               grind)
            | exact superpose b8e323 b8e20
            | exact resolve b8e20 b8e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e323
          have b8e334 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e324
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e324
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e324 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e324
          have b8e335 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e334
          have b8e336 : x = (M.op y y) := by
            first
            | (have r₁ := b8e335
               have r₂ := b8e21
               grind)
            | exact resolve b8e335 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e335
          have b8e338 : False := by grind
          exact b8e338

/-- `Equation4164`: `x ◇ y = ((y ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation4164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4164.models_iff G M).mp hM
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
      have b0e43 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
      have b0e111 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e55 x y
           grind)
        | exact superpose b0e55 b0e18
        | (have j1 := b0e55 x y
           grind)
        | exact resolve b0e18 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e118 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e460 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e117 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e117
        | (have j0 := b0e117 (τ X1) (τ X0)
           grind)
        | exact resolve b0e117 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e470 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e460 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e460
        | (have j0 := b0e460 X0 X1
           grind)
        | exact resolve b0e460 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460
      have b0e473 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e470 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e470
        | (have j0 := b0e470 X0 X1
           grind)
        | exact resolve b0e470 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e470
      have b0e475 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e473 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e473
        | (have j0 := b0e473 X0 X1
           grind)
        | exact resolve b0e473 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e473
      have b0e476 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e475 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e475
        | (have j0 := b0e475 X0 X1
           grind)
        | exact resolve b0e475 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e475
      have b0e477 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e476 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e476
        | (have j0 := b0e476 X0 X1
           grind)
        | exact resolve b0e476 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e476
      have b0e478 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e477 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e477
        | (have j0 := b0e477 X0 X1
           grind)
        | exact resolve b0e477 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e477
      have b0e494 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e118 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e118
        | (have j0 := b0e118 (τ X1) (τ X0)
           grind)
        | exact resolve b0e118 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e504 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e494 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e494
        | (have j0 := b0e494 X0 X1
           grind)
        | exact resolve b0e494 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e494
      have b0e507 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e504 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e504
        | (have j0 := b0e504 X0 X1
           grind)
        | exact resolve b0e504 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e504
      have b0e509 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e507 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e507
        | (have j0 := b0e507 X0 X1
           grind)
        | exact resolve b0e507 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e507
      have b0e510 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e509 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e509
        | (have j0 := b0e509 X0 X1
           grind)
        | exact resolve b0e509 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e509
      have b0e511 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e510 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e510
        | (have j0 := b0e510 X0 X1
           grind)
        | exact resolve b0e510 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e510
      have b0e512 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e511 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e511
        | (have j0 := b0e511 X0 X1
           grind)
        | exact resolve b0e511 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e511
      have b0e525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e111
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e111
        | (have j1 := b0e16 (σ y) (σ x)
           grind)
        | exact resolve b0e111 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111
      have b0e526 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e525
      have b0e3594 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e526
           grind)
        | exact superpose b0e526 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e526
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e526
           grind)
        | exact resolve b0e14 b0e526
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e526
      have b0e3596 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e3594
      have b0e3598 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e3596
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e3596
        | exact resolve b0e3596 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3596
      have b0e21013 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e3598
           grind)
        | exact superpose b0e3598 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e3598
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e3598
           grind)
        | exact resolve b0e15 b0e3598
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e21014 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e3598
           grind)
        | exact superpose b0e3598 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e3598
           grind)
        | exact resolve b0e14 b0e3598
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3598
      have b0e21015 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e21013
      have b0e21018 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e21014
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e21014
        | exact resolve b0e21014 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21014
      have b0e21019 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e21018
      have b0e21020 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e21015
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e21015
        | exact resolve b0e21015 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21015
      have b0e21021 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e21020
           have r₂ := b0e21019
           grind)
        | exact resolve b0e21020 b0e21019
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21019 b0e21020
      have b0e21567 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e21021
           grind)
        | exact superpose b0e21021 b0e12
        | exact resolve b0e12 b0e21021
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21021
      have b0e21715 : x = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e21567
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e21567
        | exact resolve b0e21567 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21567
      have b0e21716 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e512 y x
           grind)
        | (have r₁ := b0e21715
           have r₂ := b0e512 y x
           grind)
        | exact resolve b0e21715 b0e512
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e512 b0e21715
      have b0e21963 : (k y x) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e21716
           grind)
        | exact superpose b0e21716 b0e12
        | exact resolve b0e12 b0e21716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21716
      have b0e22111 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e21963
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e21963
        | exact resolve b0e21963 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21963
      have b0e22112 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e478 y x
           grind)
        | (have r₁ := b0e22111
           have r₂ := b0e478 y x
           grind)
        | exact resolve b0e22111 b0e478
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e478 b0e22111
      have b0e22355 : x ≠ x ∨ y = (k y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e22112
           grind)
        | exact superpose b0e22112 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e22112
           grind)
        | exact resolve b0e14 b0e22112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22356 : x ≠ y ∨ y = (M.op x y) := by grind
      have b0e22357 : y = (k y x) ∨ y = (M.op x y) := by grind
      clear b0e22355
      have b0e22797 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e117 x y
           have i₂ := b0e22357
           grind)
        | exact superpose b0e22357 b0e117
        | (have j0 := b0e117 x y
           grind)
        | exact resolve b0e117 b0e22357
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e22842 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e22797
      have b0e28321 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e22842
           grind)
        | exact superpose b0e22842 b0e18
        | exact resolve b0e18 b0e22842
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22842
      have b0e29026 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e28321
           have i₂ := b0e22112
           grind)
        | exact superpose b0e22112 b0e28321
        | exact resolve b0e28321 b0e22112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28321
      have b0e29029 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
      clear b0e29026
      have b0e29030 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e29029
           have r₂ := b0e22356
           grind)
        | exact resolve b0e29029 b0e22356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29029
      have b0e29034 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e29030
           grind)
        | exact superpose b0e29030 b0e18
        | exact resolve b0e18 b0e29030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29037 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e29030
           grind)
        | exact superpose b0e29030 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e29030
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e29030
           grind)
        | exact resolve b0e15 b0e29030
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29030
      have b0e29039 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e29037
      have b0e29043 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e29039
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e29039
        | exact resolve b0e29039 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29039
      have b0e29067 : (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e29034
           have i₂ := b0e22112
           grind)
        | exact superpose b0e22112 b0e29034
        | exact resolve b0e29034 b0e22112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22112 b0e29034
      have b0e29071 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e29067
           have r₂ := b0e22356
           grind)
        | exact resolve b0e29067 b0e22356
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22356 b0e29067
      have b0e29594 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e29043
           have i₂ := b0e22357
           grind)
        | exact superpose b0e22357 b0e29043
        | exact resolve b0e29043 b0e22357
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22357 b0e29043
      have b0e29731 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e29594
      have b0e29847 : y = (M.op x y) := by
        first
        | (have r₁ := b0e29731
           have r₂ := b0e29071
           grind)
        | exact resolve b0e29731 b0e29071
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29071 b0e29731
      have b0e30718 : y ≠ y ∨ x = y ∨ x = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e29847
           grind)
        | exact superpose b0e29847 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e29847
           grind)
        | exact resolve b0e15 b0e29847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30719 : x ≠ y ∨ y = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e29847
           grind)
        | exact superpose b0e29847 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e29847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30720 : x = (k y x) ∨ x = y := by grind
      clear b0e30718
      have b0e31231 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e118 x y
           have i₂ := b0e30720
           grind)
        | exact superpose b0e30720 b0e118
        | (have j0 := b0e118 x y
           grind)
        | exact resolve b0e118 b0e30720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e118
      have b0e31257 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e31231
      have b0e33713 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e31257
           grind)
        | exact superpose b0e31257 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e31257
           grind)
        | exact resolve b0e14 b0e31257
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31257
      have b0e33715 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e33713
      have b0e33718 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e33715
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e33715
        | exact resolve b0e33715 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33715
      have b0e34492 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e33718
           grind)
        | exact superpose b0e33718 b0e18
        | exact resolve b0e18 b0e33718
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33718
      have b0e34503 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e34492
           have i₂ := b0e29847
           grind)
        | exact superpose b0e29847 b0e34492
        | exact resolve b0e34492 b0e29847
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34492
      have b0e34504 : (σ y) = (σ (k y x)) ∨ x = y := by grind
      clear b0e34503
      have b0e34995 : (k y x) = (τ (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e34504
           grind)
        | exact superpose b0e34504 b0e12
        | exact resolve b0e12 b0e34504
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34504
      have b0e35195 : y = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e34995
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e34995
        | exact resolve b0e34995 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34995
      have b0e35196 : y = (k y x) := by
        first
        | (have r₁ := b0e35195
           have r₂ := b0e30719
           grind)
        | exact resolve b0e35195 b0e30719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30719 b0e35195
      have b0e35607 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e30720
           have i₂ := b0e35196
           grind)
        | exact superpose b0e35196 b0e30720
        | exact resolve b0e30720 b0e35196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30720 b0e35196
      have b0e35638 : x = y := by grind
      clear b0e35607
      have b0e36003 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e35638
           grind)
        | exact superpose b0e35638 b0e18
        | exact resolve b0e18 b0e35638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36005 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e35638
           grind)
        | exact superpose b0e35638 b0e20
        | exact resolve b0e20 b0e35638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36053 : y = (M.op y y) := by
        first
        | (have i₁ := b0e29847
           have i₂ := b0e35638
           grind)
        | exact superpose b0e35638 b0e29847
        | exact resolve b0e29847 b0e35638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29847 b0e35638
      have b0e36094 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e36003
           have i₂ := b0e36053
           grind)
        | exact superpose b0e36053 b0e36003
        | exact resolve b0e36003 b0e36053
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36003 b0e36053
      have b0e36099 : False := by grind
      exact b0e36099
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
        have b1e35 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e37 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e35
        have b1e38 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e37
             have r₂ := b1e23
             grind)
          | exact resolve b1e37 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e39 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e38
          | exact resolve b1e38 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e40 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e39
          | exact resolve b1e39 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e39
        have b1e41 : False := by grind
        exact b1e41
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
        have b2e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e102 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e449 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e102 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e102
          | (have j0 := b2e102 y x
             grind)
          | exact resolve b2e102 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e102
        have b2e453 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b2e449
        have b2e456 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e453
             have r₂ := b2e22
             grind)
          | exact resolve b2e453 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e453
        have b2e460 : False := by grind
        exact b2e460
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
        have b3e50 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        clear b3e50
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
          have b4e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b4e64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e36
            | exact resolve b4e36 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e94 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e47 x y
               grind)
            | exact superpose b4e47 b4e20
            | (have j1 := b4e47 x y
               grind)
            | exact resolve b4e20 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e444 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e100 (τ X1) (τ X0)
               have i₂ := b4e64 X1 X0
               grind)
            | exact superpose b4e64 b4e100
            | (have j0 := b4e100 (τ X1) (τ X0)
               grind)
            | exact resolve b4e100 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e452 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e444 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e444
            | (have j0 := b4e444 X0 X1
               grind)
            | exact resolve b4e444 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e444
          have b4e455 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e452 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e452
            | (have j0 := b4e452 X0 X1
               grind)
            | exact resolve b4e452 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e452
          have b4e457 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e455 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e455
            | (have j0 := b4e455 X0 X1
               grind)
            | exact resolve b4e455 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e455
          have b4e458 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e457 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e457
            | (have j0 := b4e457 X0 X1
               grind)
            | exact resolve b4e457 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e457
          have b4e459 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e458 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e458
            | (have j0 := b4e458 X0 X1
               grind)
            | exact resolve b4e458 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e458
          have b4e460 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e459 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e459
            | (have j0 := b4e459 X0 X1
               grind)
            | exact resolve b4e459 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e459
          have b4e474 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e101 (τ X1) (τ X0)
               have i₂ := b4e64 X1 X0
               grind)
            | exact superpose b4e64 b4e101
            | (have j0 := b4e101 (τ X1) (τ X0)
               grind)
            | exact resolve b4e101 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e483 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e474 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e474
            | (have j0 := b4e474 X0 X1
               grind)
            | exact resolve b4e474 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e474
          have b4e486 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e483 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e483
            | (have j0 := b4e483 X0 X1
               grind)
            | exact resolve b4e483 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e483
          have b4e488 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e486 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e486
            | (have j0 := b4e486 X0 X1
               grind)
            | exact resolve b4e486 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e486
          have b4e489 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e488 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e488
            | (have j0 := b4e488 X0 X1
               grind)
            | exact resolve b4e488 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e488
          have b4e490 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e489 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e489
            | (have j0 := b4e489 X0 X1
               grind)
            | exact resolve b4e489 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e489
          have b4e491 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e490 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e490
            | (have j0 := b4e490 X0 X1
               grind)
            | exact resolve b4e490 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490
          have b4e502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e94
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e94
            | (have j1 := b4e18 (σ y) (σ x)
               grind)
            | exact resolve b4e94 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94
          have b4e503 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e502
          have b4e3630 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e503
               grind)
            | exact superpose b4e503 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e503
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e503
               grind)
            | exact resolve b4e17 b4e503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e503
          have b4e3633 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e3630
          have b4e3634 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e3633
               have r₂ := b4e25
               grind)
            | exact resolve b4e3633 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3633
          have b4e3636 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e3634
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e3634
            | exact resolve b4e3634 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3634
          have b4e21573 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e3636
               grind)
            | exact superpose b4e3636 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e3636
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e3636
               grind)
            | exact resolve b4e16 b4e3636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3636
          have b4e21574 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b4e21573
          have b4e21579 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e21574
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e21574
            | exact resolve b4e21574 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21574
          have b4e22005 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e21579
               grind)
            | exact superpose b4e21579 b4e14
            | exact resolve b4e14 b4e21579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21579
          have b4e22155 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e22005
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e22005
            | exact resolve b4e22005 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22005
          have b4e22157 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e460 y x
               grind)
            | (have r₁ := b4e22155
               have r₂ := b4e460 y x
               grind)
            | exact resolve b4e22155 b4e460
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e460 b4e22155
          have b4e22398 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e22157
               grind)
            | exact superpose b4e22157 b4e14
            | exact resolve b4e14 b4e22157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22157
          have b4e22548 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e22398
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e22398
            | exact resolve b4e22398 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22398
          have b4e22549 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e491 y x
               grind)
            | (have r₁ := b4e22548
               have r₂ := b4e491 y x
               grind)
            | exact resolve b4e22548 b4e491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e491 b4e22548
          have b4e22782 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e22549
               grind)
            | exact superpose b4e22549 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22549
               grind)
            | exact resolve b4e17 b4e22549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e22785 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e22782
          have b4e22786 : x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e22785
               have r₂ := b4e26
               grind)
            | exact resolve b4e22785 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22785
          have b4e23024 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e101 x y
               have i₂ := b4e22786
               grind)
            | exact superpose b4e22786 b4e101
            | (have j0 := b4e101 x y
               grind)
            | exact resolve b4e101 b4e22786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101
          have b4e23068 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e23024
          have b4e185066 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e23068
               grind)
            | exact superpose b4e23068 b4e20
            | exact resolve b4e20 b4e23068
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23068
          have b4e186423 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e185066
               have i₂ := b4e22549
               grind)
            | exact superpose b4e22549 b4e185066
            | exact resolve b4e185066 b4e22549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22549 b4e185066
          have b4e186426 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e186423
          have b4e186427 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e186426
               have r₂ := b4e26
               grind)
            | exact resolve b4e186426 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e186426
          have b4e188126 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e186427
               grind)
            | exact superpose b4e186427 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e186427
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e186427
               grind)
            | exact resolve b4e16 b4e186427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186427
          have b4e188127 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e188126
          have b4e188132 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e188127
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e188127
            | exact resolve b4e188127 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188127
          have b4e191137 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e188132
               have i₂ := b4e22786
               grind)
            | exact superpose b4e22786 b4e188132
            | exact resolve b4e188132 b4e22786
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22786
          have b4e191175 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e188132
               grind)
            | exact superpose b4e188132 b4e14
            | exact resolve b4e14 b4e188132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188132
          have b4e191465 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e191137
          have b4e191522 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e191175
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e191175
            | exact resolve b4e191175 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191175
          have b4e191548 : x = (M.op x y) := by
            first
            | (have r₁ := b4e191465
               have r₂ := b4e25
               grind)
            | exact resolve b4e191465 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191465
          have b4e191549 : y = (k y x) := by
            first
            | (have j1 := b4e16 y x
               grind)
            | (have r₁ := b4e191522
               have r₂ := b4e16 y x
               grind)
            | exact resolve b4e191522 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191522
          have b4e194067 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e100 x y
               have i₂ := b4e191549
               grind)
            | exact superpose b4e191549 b4e100
            | (have j0 := b4e100 x y
               grind)
            | exact resolve b4e100 b4e191549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e194106 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e194067
          have b4e209162 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e194106
               grind)
            | exact superpose b4e194106 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e194106
               grind)
            | exact resolve b4e17 b4e194106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194106
          have b4e209165 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e209162
          have b4e209166 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e209165
               have r₂ := b4e25
               grind)
            | exact resolve b4e209165 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209165
          have b4e209169 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e209166
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e209166
            | exact resolve b4e209166 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209166
          have b4e209171 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e209169
               have i₂ := b4e191549
               grind)
            | exact superpose b4e191549 b4e209169
            | exact resolve b4e209169 b4e191549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191549 b4e209169
          have b4e209172 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e209171
               have r₂ := b4e25
               grind)
            | exact resolve b4e209171 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e209171
          have b4e210541 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e209172
               grind)
            | exact superpose b4e209172 b4e20
            | exact resolve b4e20 b4e209172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e209172
          have b4e210549 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e210541
               have i₂ := b4e191548
               grind)
            | exact superpose b4e191548 b4e210541
            | exact resolve b4e210541 b4e191548
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e191548 b4e210541
          have b4e210550 : False := by grind
          exact b4e210550
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
          have b5e35 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e37 : x = y ∨ y = (k x y) := by grind
          clear b5e35
          have b5e38 : y = (k x y) := by
            first
            | (have r₁ := b5e37
               have r₂ := b5e25
               grind)
            | exact resolve b5e37 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e37
          have b5e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e96 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e41 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e464 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e96 y x
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e96
            | (have j0 := b5e96 y x
               grind)
            | exact resolve b5e96 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e96
          have b5e467 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e464
          have b5e470 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e467
               have r₂ := b5e24
               grind)
            | exact resolve b5e467 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e467
          have b5e474 : False := by grind
          exact b5e474
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
        have b6e65 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
        have b6e67 : x = (M.op y x) ∨ y = (M.op y x) := by grind
        clear b6e65
        have b6e70 : y = (M.op y x) := by
          first
          | (have r₁ := b6e67
             have r₂ := b6e21
             grind)
          | exact resolve b6e67 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e73 : False := by grind
        exact b6e73
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
          have b7e35 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e37 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e35
          have b7e38 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e37
               have r₂ := b7e25
               grind)
            | exact resolve b7e37 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e37
          have b7e39 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e38
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e38
            | exact resolve b7e38 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e42 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e39
               grind)
            | exact superpose b7e39 b7e14
            | exact resolve b7e14 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e43 : y = (k x y) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e42
            | exact resolve b7e42 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e53 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e43
               grind)
            | exact superpose b7e43 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b7e53
          have b7e56 : x = (M.op y x) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e21
               grind)
            | exact resolve b7e54 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e58 : False := by grind
          exact b7e58
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e92 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e98 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e99 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e384 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e98 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e98
            | (have j0 := b8e98 (τ X1) (τ X0)
               grind)
            | exact resolve b8e98 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e391 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e384 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e384
            | (have j0 := b8e384 X0 X1
               grind)
            | exact resolve b8e384 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e384
          have b8e394 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e391 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e391
            | (have j0 := b8e391 X0 X1
               grind)
            | exact resolve b8e391 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e391
          have b8e396 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e394 X0 X1
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
          have b8e397 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e398 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e397 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e397
            | (have j0 := b8e397 X0 X1
               grind)
            | exact resolve b8e397 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e397
          have b8e399 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e398
            | (have j0 := b8e398 X0 X1
               grind)
            | exact resolve b8e398 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e398
          have b8e448 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e99 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e99
            | (have j0 := b8e99 (τ X1) (τ X0)
               grind)
            | exact resolve b8e99 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e455 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e448 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e448
            | (have j0 := b8e448 X0 X1
               grind)
            | exact resolve b8e448 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e448
          have b8e458 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e455 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e455
            | (have j0 := b8e455 X0 X1
               grind)
            | exact resolve b8e455 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e455
          have b8e460 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e458 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e458
            | (have j0 := b8e458 X0 X1
               grind)
            | exact resolve b8e458 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e458
          have b8e461 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e460 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e460
            | (have j0 := b8e460 X0 X1
               grind)
            | exact resolve b8e460 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e462 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e461 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e461
            | (have j0 := b8e461 X0 X1
               grind)
            | exact resolve b8e461 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e461
          have b8e463 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
          have b8e472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e92
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e92
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e92 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e473 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e472
          have b8e3770 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e473
               grind)
            | exact superpose b8e473 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e473
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e473
               grind)
            | exact resolve b8e17 b8e473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3772 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e473
          have b8e3773 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e3770
          have b8e3774 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e3773
               have r₂ := b8e3772
               grind)
            | exact resolve b8e3773 b8e3772
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3772 b8e3773
          have b8e3776 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3774
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3774
            | exact resolve b8e3774 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3774
          have b8e20023 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3776
               grind)
            | exact superpose b8e3776 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e3776
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3776
               grind)
            | exact resolve b8e16 b8e3776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3776
          have b8e20024 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e20023
          have b8e20028 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20024
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e20024
            | exact resolve b8e20024 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20024
          have b8e20496 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e20028
               grind)
            | exact superpose b8e20028 b8e14
            | exact resolve b8e14 b8e20028
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20028
          have b8e20645 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20496
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e20496
            | exact resolve b8e20496 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20496
          have b8e20647 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e399 y x
               grind)
            | (have r₁ := b8e20645
               have r₂ := b8e399 y x
               grind)
            | exact resolve b8e20645 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e20645
          have b8e20737 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e20647
               grind)
            | exact superpose b8e20647 b8e14
            | exact resolve b8e14 b8e20647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20647
          have b8e20887 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20737
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e20737
            | exact resolve b8e20737 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20737
          have b8e20888 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e463 y x
               grind)
            | (have r₁ := b8e20887
               have r₂ := b8e463 y x
               grind)
            | exact resolve b8e20887 b8e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463 b8e20887
          have b8e21123 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e20888
               grind)
            | exact superpose b8e20888 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e20888
               grind)
            | exact resolve b8e17 b8e20888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21125 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e21126 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e21123
          have b8e21127 : x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e21126
               have r₂ := b8e21125
               grind)
            | exact resolve b8e21126 b8e21125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21126
          have b8e21597 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e99 x y
               have i₂ := b8e21127
               grind)
            | exact superpose b8e21127 b8e99
            | (have j0 := b8e99 x y
               grind)
            | exact resolve b8e99 b8e21127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e21641 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e21597
          have b8e176773 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e21641
               grind)
            | exact superpose b8e21641 b8e20
            | exact resolve b8e20 b8e21641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21641
          have b8e180018 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e176773
               have i₂ := b8e20888
               grind)
            | exact superpose b8e20888 b8e176773
            | exact resolve b8e176773 b8e20888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e176773
          have b8e180021 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e180018
          have b8e180022 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e180021
               have r₂ := b8e21125
               grind)
            | exact resolve b8e180021 b8e21125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180021
          have b8e181645 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e180022
               grind)
            | exact superpose b8e180022 b8e20
            | exact resolve b8e20 b8e180022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e181648 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e180022
               grind)
            | exact superpose b8e180022 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e180022
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e180022
               grind)
            | exact resolve b8e16 b8e180022
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e180022
          have b8e181649 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e181648
          have b8e181654 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e181649
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e181649
            | exact resolve b8e181649 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181649
          have b8e183278 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e181645
               have i₂ := b8e20888
               grind)
            | exact superpose b8e20888 b8e181645
            | exact resolve b8e181645 b8e20888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20888 b8e181645
          have b8e183282 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e183278
               have r₂ := b8e21125
               grind)
            | exact resolve b8e183278 b8e21125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21125 b8e183278
          have b8e186265 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e181654
               have i₂ := b8e21127
               grind)
            | exact superpose b8e21127 b8e181654
            | exact resolve b8e181654 b8e21127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21127
          have b8e186303 : (k y x) = (τ (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e181654
               grind)
            | exact superpose b8e181654 b8e14
            | exact resolve b8e14 b8e181654
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181654
          have b8e186593 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e186265
          have b8e186650 : y = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e186303
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e186303
            | exact resolve b8e186303 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186303
          have b8e186677 : x = (M.op x y) := by
            first
            | (have r₁ := b8e186593
               have r₂ := b8e183282
               grind)
            | exact resolve b8e186593 b8e183282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e183282 b8e186593
          have b8e186678 : y = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e186650
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e186650 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186650
          have b8e189205 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e98 x y
               have i₂ := b8e186678
               grind)
            | exact superpose b8e186678 b8e98
            | (have j0 := b8e98 x y
               grind)
            | exact resolve b8e98 b8e186678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98
          have b8e189244 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e189205
          have b8e204078 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e189244
               grind)
            | exact superpose b8e189244 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e189244
               grind)
            | exact resolve b8e17 b8e189244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e204080 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e189244
          have b8e204081 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e204078
          have b8e204082 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e204081
               have r₂ := b8e204080
               grind)
            | exact resolve b8e204081 b8e204080
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204081
          have b8e204085 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e204082
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e204082
            | exact resolve b8e204082 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204082
          have b8e204087 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e204085
               have i₂ := b8e186678
               grind)
            | exact superpose b8e186678 b8e204085
            | exact resolve b8e204085 b8e186678
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186678 b8e204085
          have b8e204088 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e204087
               have r₂ := b8e204080
               grind)
            | exact resolve b8e204087 b8e204080
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204080 b8e204087
          have b8e205428 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e204088
               grind)
            | exact superpose b8e204088 b8e20
            | exact resolve b8e20 b8e204088
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204088
          have b8e205436 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e205428
               have i₂ := b8e186677
               grind)
            | exact superpose b8e186677 b8e205428
            | exact resolve b8e205428 b8e186677
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186677 b8e205428
          have b8e205437 : False := by grind
          exact b8e205437
