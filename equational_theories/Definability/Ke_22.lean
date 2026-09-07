import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation655`: `x = x ◇ (y ◇ ((z ◇ y) ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation655 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law655 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law655.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e60 : False := by grind
      exact b0e60
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e45 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e48 : x = y ∨ y = (k x y) := by grind
          clear b5e45
          have b5e49 : y = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e189 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e8175 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e189 x y
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e189
            | (have j0 := b5e189 x y
               grind)
            | exact resolve b5e189 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e189
          have b5e8178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e8175
          have b5e8181 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e8178
               have r₂ := b5e24
               grind)
            | exact resolve b5e8178 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8178
          have b5e8185 : False := by grind
          exact b5e8185
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
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b7e57 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e47
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e47 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e58 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e26
               grind)
            | exact resolve b7e57 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e57
          have b7e59 : x = y := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e22
               grind)
            | exact resolve b7e58 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e60 : False := by grind
          exact b7e60
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b8e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e157 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e147
               have r₂ := b8e24
               grind)
            | exact resolve b8e147 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e161 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e157
               have r₂ := b8e23
               grind)
            | exact resolve b8e157 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157
          have b8e190 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e161
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e161
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e161
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e161
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e161 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161
          have b8e191 : y = (M.op x y) ∨ x = y := by grind
          clear b8e190
          have b8e192 : x = y := by
            first
            | (have r₁ := b8e191
               have r₂ := b8e22
               grind)
            | exact resolve b8e191 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e191
          have b8e193 : False := by grind
          exact b8e193

/-- `Equation72`: `x = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_x_x_pyx_Equation72 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law72 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law72.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (M.op X0 X0) (M.op X0 X0)
           have i₂ := b0e11 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e31 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
           have i₂ := b0e22 (M.op X0 X0)
           grind)
        | exact superpose b0e22 b0e11
        | exact resolve b0e11 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op X0 (τ X1)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e29 X1 X0
           have i₂ := b0e16 (τ X1) X0
           grind)
        | exact superpose b0e16 b0e29
        | (have j1 := b0e16 (τ X1) X0
           grind)
        | exact resolve b0e29 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e46 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e52 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e46 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e52 X0 X1
           have j1 := b0e14 X0 X1
           grind)
        | (have r₁ := b0e52 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e52 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e64 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e53 (σ X0) (σ X1)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e53
        | exact resolve b0e53 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e752 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op (M.op X0 X0) (M.op X0 X0)) X1
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e755 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e22 (M.op (M.op X0 X0) (M.op X0 X0))
           have i₂ := b0e31 X0
           grind)
        | exact superpose b0e31 b0e22
        | exact resolve b0e22 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e31
      have b0e1032 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e755 X1
           have i₂ := b0e752 X1 X0
           grind)
        | exact superpose b0e752 b0e755
        | exact resolve b0e755 b0e752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e755
      have b0e1035 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X1 X1)
           have i₂ := b0e752 X1 X0
           grind)
        | exact superpose b0e752 b0e11
        | exact resolve b0e11 b0e752
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1298 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
        first
        | (have i₁ := b0e1032 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1032
        | exact resolve b0e1032 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1303 : x = (M.op x (M.op y y)) := by
        first
        | (have i₁ := b0e1032 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1032
        | exact resolve b0e1032 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1032
      have b0e1390 : y = (M.op x x) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e1303
           grind)
        | exact superpose b0e1303 b0e11
        | exact resolve b0e11 b0e1303
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1303
      have b0e1429 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
        intro X0
        first
        | (have i₁ := b0e11 x X0
           have i₂ := b0e1390
           grind)
        | exact superpose b0e1390 b0e11
        | exact resolve b0e11 b0e1390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1445 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e752 x x
           have i₂ := b0e1390
           grind)
        | exact superpose b0e1390 b0e752
        | exact resolve b0e752 b0e1390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1390
      have b0e1468 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e44 X0 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e44
        | exact resolve b0e44 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e1576 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1468 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1468
        | (have j0 := b0e1468 X0 X1
           grind)
        | exact resolve b0e1468 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1468
      have b0e4394 : (σ y) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e11 (σ y) (σ x)
           have i₂ := b0e1298
           grind)
        | exact superpose b0e1298 b0e11
        | exact resolve b0e11 b0e1298
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1298
      have b0e4738 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e752 (σ x) (σ x)
           have i₂ := b0e4394
           grind)
        | exact superpose b0e4394 b0e752
        | exact resolve b0e752 b0e4394
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e752
      have b0e5974 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e4738
           grind)
        | exact superpose b0e4738 b0e18
        | exact resolve b0e18 b0e4738
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4738
      have b0e6006 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e5974
           have i₂ := b0e1445
           grind)
        | exact superpose b0e1445 b0e5974
        | exact resolve b0e5974 b0e1445
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1445 b0e5974
      have b0e6571 : (σ (k y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (k y y)) := by
        first
        | (have i₁ := b0e6006
           have i₂ := b0e64 y y
           grind)
        | exact superpose b0e64 b0e6006
        | (have j1 := b0e64 y y
           grind)
        | exact resolve b0e6006 b0e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e87780 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e6571
           have i₂ := b0e1576 y y
           grind)
        | exact superpose b0e1576 b0e6571
        | (have j1 := b0e1576 y y
           grind)
        | (have r₁ := b0e6571
           have r₂ := b0e1576 y y
           grind)
        | exact resolve b0e6571 b0e1576
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1576 b0e6571
      have b0e87781 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
      clear b0e87780
      have b0e87782 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
      clear b0e87781
      have b0e87804 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e12 (M.op y y)
           have i₂ := b0e87782
           grind)
        | exact superpose b0e87782 b0e12
        | exact resolve b0e12 b0e87782
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87782
      have b0e87871 : y = (M.op y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e87804
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e87804
        | exact resolve b0e87804 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87804
      have b0e87872 : y = (M.op y y) := by grind
      clear b0e87871
      have b0e89039 : y = (M.op y (M.op y y)) := by
        first
        | (have i₁ := b0e1035 y y
           have i₂ := b0e87872
           grind)
        | exact superpose b0e87872 b0e1035
        | exact resolve b0e1035 b0e87872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1035
      have b0e89121 : x = y := by
        first
        | (have i₁ := b0e89039
           have i₂ := b0e1429 y
           grind)
        | exact superpose b0e1429 b0e89039
        | exact resolve b0e89039 b0e1429
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1429 b0e89039
      have b0e89239 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e4394
           have i₂ := b0e89121
           grind)
        | exact superpose b0e89121 b0e4394
        | exact resolve b0e4394 b0e89121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4394 b0e89121
      have b0e93088 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e6006
           have i₂ := b0e89239
           grind)
        | exact superpose b0e89239 b0e6006
        | exact resolve b0e6006 b0e89239
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6006 b0e89239
      have b0e93323 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e93088
           have i₂ := b0e87872
           grind)
        | exact superpose b0e87872 b0e93088
        | exact resolve b0e93088 b0e87872
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87872 b0e93088
      have b0e93324 : False := by grind
      exact b0e93324
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b1e12 X0 (M.op X0 X0)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e12 (σ x) (σ x)
             have i₂ := b1e24 (σ x)
             grind)
          | exact superpose b1e24 b1e12
          | exact resolve b1e12 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e38 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e19
          | exact resolve b1e19 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b1e58 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e63 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b1e58 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e64 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b1e63 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e63 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e63 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e68 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b1e25 (M.op X0 X0)
             grind)
          | exact superpose b1e25 b1e12
          | exact resolve b1e12 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e255 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e53 y y
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e53
          | exact resolve b1e53 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e318 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b1e255
        have b1e349 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e318
             grind)
          | exact superpose b1e318 b1e13
          | exact resolve b1e13 b1e318
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e318
        have b1e363 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e349
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e349
          | exact resolve b1e349 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e349
        have b1e422 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e64 y y
             have i₂ := b1e363
             grind)
          | exact superpose b1e363 b1e64
          | exact resolve b1e64 b1e363
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e363
        have b1e974 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op (M.op X0 X0) (M.op X0 X0)) X1
             have i₂ := b1e68 X0
             grind)
          | exact superpose b1e68 b1e12
          | exact resolve b1e12 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e977 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e25 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b1e68 X0
             grind)
          | exact superpose b1e68 b1e25
          | exact resolve b1e25 b1e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e68
        have b1e1693 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e977 X1
             have i₂ := b1e974 X1 X0
             grind)
          | exact superpose b1e974 b1e977
          | exact resolve b1e977 b1e974
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e977
        have b1e2118 : x = (M.op x (M.op y y)) := by
          first
          | (have i₁ := b1e1693 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1693
          | exact resolve b1e1693 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1693
        have b1e2194 : y = (M.op x x) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e2118
             grind)
          | exact superpose b1e2118 b1e12
          | exact resolve b1e12 b1e2118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2118
        have b1e2288 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b1e974 x x
             have i₂ := b1e2194
             grind)
          | exact superpose b1e2194 b1e974
          | exact resolve b1e974 b1e2194
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e974
        have b1e2531 : (σ x) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e2288
             grind)
          | exact superpose b1e2288 b1e38
          | exact resolve b1e38 b1e2288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2288
        have b1e9525 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e2531
             have i₂ := b1e422
             grind)
          | exact superpose b1e422 b1e2531
          | exact resolve b1e2531 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422 b1e2531
        have b1e9559 : (σ x) = (σ y) ∨ x = y := by grind
        clear b1e9525
        have b1e10217 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e9559
             grind)
          | exact superpose b1e9559 b1e13
          | exact resolve b1e13 b1e9559
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9559
        have b1e10303 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e10217
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e10217
          | exact resolve b1e10217 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10217
        have b1e10304 : x = y := by grind
        clear b1e10303
        have b1e10584 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e38
             have i₂ := b1e10304
             grind)
          | exact superpose b1e10304 b1e38
          | exact resolve b1e38 b1e10304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e10607 : y = (M.op y y) := by
          first
          | (have i₁ := b1e2194
             have i₂ := b1e10304
             grind)
          | exact superpose b1e10304 b1e2194
          | exact resolve b1e2194 b1e10304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2194 b1e10304
        have b1e10634 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e10584
             have i₂ := b1e10607
             grind)
          | exact superpose b1e10607 b1e10584
          | exact resolve b1e10584 b1e10607
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e10584 b1e10607
        have b1e10635 : False := by grind
        exact b1e10635
      · have b2e12 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b2e12 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b2e12 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e25 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b2e24 (M.op X0 X0)
             grind)
          | exact superpose b2e24 b2e12
          | exact resolve b2e12 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e26 : y ≠ y ∨ x = (k x y) := by
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
        have b2e30 : x = (k x y) := by grind
        clear b2e26
        have b2e57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e24 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e24 X0
             have i₂ := b2e17 (M.op X0 X0) X1
             grind)
          | exact superpose b2e17 b2e24
          | (have j1 := b2e17 X0 X1
             grind)
          | exact resolve b2e24 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e61 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
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
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e168 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e61 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e169 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e168
             have r₂ := b2e21
             grind)
          | exact resolve b2e168 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e168
        have b2e170 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e169
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e169
          | exact resolve b2e169 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e169
        have b2e171 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e170
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e170
          | exact resolve b2e170 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e170
        have b2e172 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e21
          | exact resolve b2e21 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e827 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op (M.op X0 X0) (M.op X0 X0)) X1
             have i₂ := b2e25 X0
             grind)
          | exact superpose b2e25 b2e12
          | exact resolve b2e12 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e829 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
          intro X0
          grind
        clear b2e25
        have b2e838 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have j0 := b2e829 X0
             have j1 := b2e15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b2e829 X0
             have r₂ := b2e15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b2e829 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e829
        have b2e1120 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e838 X1
             have i₂ := b2e827 X1 X0
             grind)
          | exact superpose b2e827 b2e838
          | exact resolve b2e838 b2e827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e838
        have b2e1201 : (σ x) = (k (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b2e1120 (σ y) (σ x)
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e1120
          | exact resolve b2e1120 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1120
        have b2e1236 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e1201
             have i₂ := b2e171
             grind)
          | exact superpose b2e171 b2e1201
          | exact resolve b2e1201 b2e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e171 b2e1201
        have b2e1246 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e1236
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e1236
          | exact resolve b2e1236 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1236
        have b2e1391 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e1246
             grind)
          | exact superpose b2e1246 b2e13
          | exact resolve b2e13 b2e1246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1246
        have b2e1430 : x = (k x x) := by
          first
          | (have i₁ := b2e1391
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1391
          | exact resolve b2e1391 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1391
        have b2e1517 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e57 x x
             have i₂ := b2e1430
             grind)
          | exact superpose b2e1430 b2e57
          | (have j0 := b2e57 x x
             grind)
          | exact resolve b2e57 b2e1430
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e1430
        have b2e1518 : x = (M.op x x) := by grind
        clear b2e1517
        have b2e1565 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e12 x X0
             have i₂ := b2e1518
             grind)
          | exact superpose b2e1518 b2e12
          | exact resolve b2e12 b2e1518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1751 : x = (M.op y y) := by
          first
          | (have i₁ := b2e1565 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1565
          | exact resolve b2e1565 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1565
        have b2e1803 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b2e827 y y
             have i₂ := b2e1751
             grind)
          | exact superpose b2e1751 b2e827
          | exact resolve b2e827 b2e1751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e827 b2e1751
        have b2e1808 : x = (M.op y x) := by
          first
          | (have i₁ := b2e1803
             have i₂ := b2e1518
             grind)
          | exact superpose b2e1518 b2e1803
          | exact resolve b2e1803 b2e1518
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1518 b2e1803
        have b2e1817 : x = y := by
          first
          | (have i₁ := b2e1808
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1808
          | exact resolve b2e1808 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1808
        have b2e1891 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e172
             have i₂ := b2e1817
             grind)
          | exact superpose b2e1817 b2e172
          | exact resolve b2e172 b2e1817
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e172 b2e1817
        have b2e1898 : False := by grind
        exact b2e1898
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e12 y X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b3e12 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e26 : x = (M.op x y) := by
          first
          | (have i₁ := b3e12 x x
             have i₂ := b3e24 x
             grind)
          | exact superpose b3e24 b3e12
          | exact resolve b3e12 b3e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b3e52 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b3e56 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e52 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e57 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          first
          | (have j0 := b3e56 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e56 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e56 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e61 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b3e25 (M.op X0 X0)
             grind)
          | exact superpose b3e25 b3e12
          | exact resolve b3e12 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e62 : y = (M.op (M.op x x) (M.op x x)) := by
          first
          | (have i₁ := b3e24 (M.op x x)
             have i₂ := b3e25 x
             grind)
          | exact superpose b3e25 b3e24
          | exact resolve b3e24 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e79 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e12 (M.op x x) X0
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e12
          | exact resolve b3e12 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e148 : (M.op y x) = (M.op x x) := by
          first
          | (have i₁ := b3e79 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e79
          | exact resolve b3e79 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e945 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op (M.op X0 X0) (M.op X0 X0)) X1
             have i₂ := b3e61 X0
             grind)
          | exact superpose b3e61 b3e12
          | exact resolve b3e12 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e948 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e25 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b3e61 X0
             grind)
          | exact superpose b3e61 b3e25
          | exact resolve b3e25 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e61
        have b3e1255 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e948 X1
             have i₂ := b3e945 X1 X0
             grind)
          | exact superpose b3e945 b3e948
          | exact resolve b3e948 b3e945
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e945 b3e948
        have b3e1524 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
          first
          | (have i₁ := b3e1255 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e1255
          | exact resolve b3e1255 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1255
        have b3e3097 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e12 (σ y) (σ x)
             have i₂ := b3e1524
             grind)
          | exact superpose b3e1524 b3e12
          | exact resolve b3e12 b3e1524
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1524
        have b3e3118 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e48 x x
             have i₂ := b3e3097
             grind)
          | exact superpose b3e3097 b3e48
          | exact resolve b3e48 b3e3097
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e3097
        have b3e3148 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e3118
        have b3e6691 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3148
             grind)
          | exact superpose b3e3148 b3e13
          | exact resolve b3e13 b3e3148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3148
        have b3e6755 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e6691
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e6691
          | exact resolve b3e6691 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6691
        have b3e7039 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e57 x x
             have i₂ := b3e6755
             grind)
          | exact superpose b3e6755 b3e57
          | exact resolve b3e57 b3e6755
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e6755
        have b3e7060 : y = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7039
             have i₂ := b3e148
             grind)
          | exact superpose b3e148 b3e7039
          | exact resolve b3e7039 b3e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e148 b3e7039
        have b3e7085 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e7060
             have r₂ := b3e20
             grind)
          | exact resolve b3e7060 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7060
        have b3e7232 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b3e13 x
             have i₂ := b3e7085
             grind)
          | exact superpose b3e7085 b3e13
          | exact resolve b3e13 b3e7085
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7085
        have b3e7289 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e7232
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e7232
          | exact resolve b3e7232 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7232
        have b3e7290 : x = y := by grind
        clear b3e7289
        have b3e7898 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e7290
             grind)
          | exact superpose b3e7290 b3e20
          | exact resolve b3e20 b3e7290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e7901 : y = (M.op y y) := by
          first
          | (have i₁ := b3e26
             have i₂ := b3e7290
             grind)
          | exact superpose b3e7290 b3e26
          | exact resolve b3e26 b3e7290
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26 b3e7290
        have b3e7955 : False := by grind
        exact b3e7955
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : x = (M.op x y) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e26 x
               grind)
            | exact superpose b4e26 b4e13
            | exact resolve b4e13 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e60 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e13 (σ x) (σ x)
               have i₂ := b4e27 (σ x)
               grind)
            | exact superpose b4e27 b4e13
            | exact resolve b4e13 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e62 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e60
               grind)
            | exact superpose b4e60 b4e20
            | exact resolve b4e20 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e66 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e33
               grind)
            | exact superpose b4e33 b4e62
            | exact resolve b4e62 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e62
          have b4e67 : False := by grind
          exact b4e67
        · have b5e13 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e13 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : x ≠ y ∨ y = (k y y) := by
            first
            | (have i₁ := b5e16 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e16
            | (have j0 := b5e16 y y
               grind)
            | exact resolve b5e16 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b5e36 : x = (k x y) ∨ y = (M.op y x) := by grind
          have b5e37 : x = (k x y) := by
            first
            | (have r₁ := b5e36
               have r₂ := b5e21
               grind)
            | exact resolve b5e36 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e49 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
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
          have b5e54 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e16 X0 (M.op X0 X0)
               have i₂ := b5e27 X0
               grind)
            | exact superpose b5e27 b5e16
            | (have j0 := b5e16 X0 (M.op X0 X0)
               grind)
            | (have r₁ := b5e16 X0 (M.op X0 X0)
               have r₂ := b5e27 X0
               grind)
            | exact resolve b5e16 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e57 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e54 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e83 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k X0 (τ X1))
               have i₂ := b5e33 X1 X0
               grind)
            | exact superpose b5e33 b5e14
            | exact resolve b5e14 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e146 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e49 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e147 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e146
               have r₂ := b5e23
               grind)
            | exact resolve b5e146 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146
          have b5e148 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e147
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e147
            | exact resolve b5e147 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147
          have b5e149 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e148
               have i₂ := b5e37
               grind)
            | exact superpose b5e37 b5e148
            | exact resolve b5e148 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e148
          have b5e185 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e42 y y
               grind)
            | exact superpose b5e42 b5e24
            | (have j1 := b5e42 y y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e42 y x
               grind)
            | exact resolve b5e24 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e216 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e185
          have b5e329 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e149
               grind)
            | exact superpose b5e149 b5e23
            | exact resolve b5e23 b5e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e371 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e83 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e57 (σ X0)
               grind)
            | exact superpose b5e57 b5e83
            | exact resolve b5e83 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57 b5e83
          have b5e380 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e371 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e371
            | exact resolve b5e371 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e371
          have b5e819 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e216
               have i₂ := b5e18 y y
               grind)
            | exact superpose b5e18 b5e216
            | (have j1 := b5e18 (σ y) (σ y)
               grind)
            | exact resolve b5e216 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e216
          have b5e820 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e819
          have b5e821 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e820
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e820
            | exact resolve b5e820 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e820
          have b5e822 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
          clear b5e821
          have b5e829 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b5e822
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e822
            | exact resolve b5e822 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e822
          have b5e879 : y = (k y (τ (σ y))) ∨ x = y := by
            first
            | (have i₁ := b5e380 y
               have i₂ := b5e829
               grind)
            | exact superpose b5e829 b5e380
            | exact resolve b5e380 b5e829
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e380 b5e829
          have b5e898 : y = (k y y) ∨ x = y := by
            first
            | (have i₁ := b5e879
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e879
            | exact resolve b5e879 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e879
          have b5e900 : y = (k y y) := by
            first
            | (have r₁ := b5e898
               have r₂ := b5e28
               grind)
            | exact resolve b5e898 b5e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28 b5e898
          have b5e969 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e18 y y
               have i₂ := b5e900
               grind)
            | exact superpose b5e900 b5e18
            | (have j0 := b5e18 y y
               grind)
            | exact resolve b5e18 b5e900
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e900
          have b5e970 : y = (M.op y y) := by grind
          clear b5e969
          have b5e1008 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e970
               grind)
            | exact superpose b5e970 b5e22
            | exact resolve b5e22 b5e970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e970
          have b5e1109 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e329
               have i₂ := b5e1008
               grind)
            | exact superpose b5e1008 b5e329
            | exact resolve b5e329 b5e1008
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e329 b5e1008
          have b5e1110 : False := by grind
          exact b5e1110
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b6e12 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e25 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b6e24 (M.op X0 X0)
             grind)
          | exact superpose b6e24 b6e12
          | exact resolve b6e12 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e26 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e30 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e26
        have b6e31 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b6e30
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e30
          | exact resolve b6e30 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e32 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e31
             grind)
          | exact superpose b6e31 b6e13
          | exact resolve b6e13 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e33 : x = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b6e51 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e33
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e33
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e33 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e62 : x = (M.op y x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e51
             have r₂ := b6e21
             grind)
          | exact resolve b6e51 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e65 : x = (M.op y x) := by
          first
          | (have r₁ := b6e62
             have r₂ := b6e20
             grind)
          | exact resolve b6e62 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e67 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e20
          | exact resolve b6e20 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e216 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e49 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e218 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e216 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e216
        have b6e793 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (M.op (M.op X0 X0) (M.op X0 X0)) X1
             have i₂ := b6e25 X0
             grind)
          | exact superpose b6e25 b6e12
          | exact resolve b6e12 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e795 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) := by
          intro X0
          grind
        have b6e796 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have i₁ := b6e24 (M.op (M.op X0 X0) (M.op X0 X0))
             have i₂ := b6e25 X0
             grind)
          | exact superpose b6e25 b6e24
          | exact resolve b6e24 b6e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24 b6e25
        have b6e804 : ∀ X0 : G, (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
          intro X0
          first
          | (have j0 := b6e795 X0
             have j1 := b6e15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | (have r₁ := b6e795 X0
             have r₂ := b6e15 X0 (M.op (M.op X0 X0) (M.op X0 X0))
             grind)
          | exact resolve b6e795 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e795
        have b6e1095 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e804 X1
             have i₂ := b6e793 X1 X0
             grind)
          | exact superpose b6e793 b6e804
          | exact resolve b6e804 b6e793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e804
        have b6e1096 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e796 X1
             have i₂ := b6e793 X1 X0
             grind)
          | exact superpose b6e793 b6e796
          | exact resolve b6e796 b6e793
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e793 b6e796
        have b6e1210 : x = (k x (M.op y x)) := by
          first
          | (have i₁ := b6e1095 y x
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e1095
          | exact resolve b6e1095 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1095
        have b6e1237 : x = (k x x) := by
          first
          | (have i₁ := b6e1210
             have i₂ := b6e65
             grind)
          | exact superpose b6e65 b6e1210
          | exact resolve b6e1210 b6e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e65 b6e1210
        have b6e1301 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e218 x
             have i₂ := b6e1237
             grind)
          | exact superpose b6e1237 b6e218
          | (have j0 := b6e218 x
             grind)
          | exact resolve b6e218 b6e1237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e218 b6e1237
        have b6e1310 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b6e1301
        have b6e1623 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) X0
             have i₂ := b6e1310
             grind)
          | exact superpose b6e1310 b6e12
          | exact resolve b6e12 b6e1310
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1310
        have b6e1844 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e1623 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1623
          | exact resolve b6e1623 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2013 : (σ y) = (M.op (σ y) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b6e1096 (σ y) (σ y)
             have i₂ := b6e1844
             grind)
          | exact superpose b6e1844 b6e1096
          | exact resolve b6e1096 b6e1844
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1096 b6e1844
        have b6e2026 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2013
             have i₂ := b6e1623 (σ y)
             grind)
          | exact superpose b6e1623 b6e2013
          | exact resolve b6e2013 b6e1623
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1623 b6e2013
        have b6e2144 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e2026
             grind)
          | exact superpose b6e2026 b6e13
          | exact resolve b6e13 b6e2026
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2026
        have b6e2180 : x = y := by
          first
          | (have i₁ := b6e2144
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2144
          | exact resolve b6e2144 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2144
        have b6e2186 : False := by grind
        exact b6e2186
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e45 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ x) = (σ (k x y)) := by
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
          have b7e52 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b7e56 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e61 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e62 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e61 X0 X1
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e61 X0 X1
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e61 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e66 : (k x y) = (τ (σ x)) := by
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
          have b7e67 : x = (k x y) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e66
            | exact resolve b7e66 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e79 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e80 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e79
               have r₂ := b7e22
               grind)
            | exact resolve b7e79 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79
          have b7e82 : x = (M.op y x) := by
            first
            | (have r₁ := b7e80
               have r₂ := b7e21
               grind)
            | exact resolve b7e80 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e89 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e82
               grind)
            | exact superpose b7e82 b7e21
            | exact resolve b7e21 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e228 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e52 y y
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e52
            | exact resolve b7e52 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e288 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
          clear b7e228
          have b7e466 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e288
               grind)
            | exact superpose b7e288 b7e14
            | exact resolve b7e14 b7e288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e288
          have b7e480 : x = (k y y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e466
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e466
            | exact resolve b7e466 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e466
          have b7e487 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e62 y y
               have i₂ := b7e480
               grind)
            | exact superpose b7e480 b7e62
            | exact resolve b7e62 b7e480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e480
          have b7e492 : x = y ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e487
               have r₂ := b7e22
               grind)
            | exact resolve b7e487 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e487
          have b7e499 : (σ x) = (σ y) := by
            first
            | (have r₁ := b7e492
               have r₂ := b7e89
               grind)
            | exact resolve b7e492 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e492
          have b7e532 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e499
               grind)
            | exact superpose b7e499 b7e14
            | exact resolve b7e14 b7e499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e499
          have b7e549 : x = y := by
            first
            | (have i₁ := b7e532
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e532
            | exact resolve b7e532 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e532
          have b7e555 : False := by grind
          exact b7e555
        · have b8e13 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e26 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b8e13 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b8e13 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e28 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               have i₂ := b8e26 (M.op X0 X0)
               grind)
            | exact superpose b8e26 b8e13
            | exact resolve b8e13 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e51 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e53 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e26 X0
               have i₂ := b8e18 (M.op X0 X0) X1
               grind)
            | exact superpose b8e18 b8e26
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e26 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e53 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e60 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e60 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e60 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e61 (σ X0) (σ X1)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e61
            | exact resolve b8e61 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e75 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (k X1 (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1
               have i₂ := b8e61 X1 (τ X0)
               grind)
            | exact superpose b8e61 b8e32
            | (have j1 := b8e61 X1 (τ X0)
               grind)
            | exact resolve b8e32 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e79 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e61 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e216 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 (σ X0)
               have i₂ := b8e51 X0 X1
               grind)
            | exact superpose b8e51 b8e26
            | (have j1 := b8e51 X1 X0
               grind)
            | exact resolve b8e26 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e714 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e75 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e75
            | exact resolve b8e75 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75
          have b8e754 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e714 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e714
            | (have j0 := b8e714 X0 X1
               grind)
            | exact resolve b8e714 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e714
          have b8e816 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op (M.op X0 X0) (M.op X0 X0)) X1
               have i₂ := b8e28 X0
               grind)
            | exact superpose b8e28 b8e13
            | exact resolve b8e13 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e819 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e26 (M.op (M.op X0 X0) (M.op X0 X0))
               have i₂ := b8e28 X0
               grind)
            | exact superpose b8e28 b8e26
            | exact resolve b8e26 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e28
          have b8e928 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72 y x
               grind)
            | exact superpose b8e72 b8e20
            | (have j1 := b8e72 y x
               grind)
            | exact resolve b8e20 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e1103 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e816 X1 X2
               have i₂ := b8e816 X1 X0
               grind)
            | exact superpose b8e816 b8e816
            | exact resolve b8e816 b8e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1117 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e819 X1
               have i₂ := b8e816 X1 X0
               grind)
            | exact superpose b8e816 b8e819
            | exact resolve b8e819 b8e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e819
          have b8e1121 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op X1 X1) X2
               have i₂ := b8e816 X1 X0
               grind)
            | exact superpose b8e816 b8e13
            | exact resolve b8e13 b8e816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e816
          have b8e2683 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1121 X1 X2 X1
               have i₂ := b8e1103 X1 (M.op X1 X2) X0
               grind)
            | (have i₁ := b8e1121 X1 X2 X1
               have i₂ := b8e1103 X0 (M.op X1 X2) X1
               grind)
            | exact superpose b8e1103 b8e1121
            | exact resolve b8e1121 b8e1103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1103 b8e1121
          have b8e3240 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e216 y x
               grind)
            | exact superpose b8e216 b8e20
            | (have j1 := b8e216 y x
               grind)
            | exact resolve b8e20 b8e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216
          have b8e3343 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e3240
               have r₂ := b8e23
               grind)
            | exact resolve b8e3240 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3240
          have b8e21804 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e928
               have i₂ := b8e754 x y
               grind)
            | exact superpose b8e754 b8e928
            | (have j1 := b8e754 x y
               grind)
            | (have r₁ := b8e928
               have r₂ := b8e754 x y
               grind)
            | exact resolve b8e928 b8e754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e754 b8e928
          have b8e21806 : (σ (M.op x y)) = (σ y) ∨ y = (k y x) := by grind
          clear b8e21804
          have b8e22531 : (M.op x y) = (τ (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e21806
               grind)
            | exact superpose b8e21806 b8e14
            | exact resolve b8e14 b8e21806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21806
          have b8e22641 : y = (M.op x y) ∨ y = (k y x) := by
            first
            | (have i₁ := b8e22531
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e22531
            | exact resolve b8e22531 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22531
          have b8e22642 : y = (k y x) := by
            first
            | (have j1 := b8e79 y x
               grind)
            | (have r₁ := b8e22641
               have r₂ := b8e79 y x
               grind)
            | exact resolve b8e22641 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79 b8e22641
          have b8e22882 : y = (M.op x y) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e55 y x
               have i₂ := b8e22642
               grind)
            | exact superpose b8e22642 b8e55
            | (have j0 := b8e55 y x
               grind)
            | exact resolve b8e55 b8e22642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e22888 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e22882
               have r₂ := b8e21
               grind)
            | exact resolve b8e22882 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22882
          have b8e23159 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 x))) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b8e2683 X0 x y
               have i₂ := b8e22888
               grind)
            | exact superpose b8e22888 b8e2683
            | exact resolve b8e2683 b8e22888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22888
          have b8e23169 : x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e23159 x
               have i₂ := b8e1117 x x
               grind)
            | exact superpose b8e1117 b8e23159
            | exact resolve b8e23159 b8e1117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23159
          have b8e23172 : y = (M.op x y) := by
            first
            | (have r₁ := b8e23169
               have r₂ := b8e22
               grind)
            | exact resolve b8e23169 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23169
          have b8e23707 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e3343
               have i₂ := b8e22642
               grind)
            | exact superpose b8e22642 b8e3343
            | exact resolve b8e3343 b8e22642
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3343 b8e22642
          have b8e23735 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e23707
               have i₂ := b8e23172
               grind)
            | exact superpose b8e23172 b8e23707
            | exact resolve b8e23707 b8e23172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23172 b8e23707
          have b8e23736 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e23735
          have b8e24916 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op X0 (σ x)))) := by
            intro X0
            first
            | (have i₁ := b8e2683 X0 (σ x) (σ y)
               have i₂ := b8e23736
               grind)
            | exact superpose b8e23736 b8e2683
            | exact resolve b8e2683 b8e23736
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2683 b8e23736
          have b8e24926 : (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b8e24916 x
               have i₂ := b8e1117 x (σ x)
               grind)
            | exact superpose b8e1117 b8e24916
            | exact resolve b8e24916 b8e1117
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1117 b8e24916
          have b8e24950 : False := by grind
          exact b8e24950

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_x_pyy_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
           have i₂ := b0e11 X0 X2 X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e867 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 X0 X2 X0 X1
           have i₂ := b0e11 X0 X0 X1
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e920 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X1 x
           have i₂ := b0e867 X1 x X0
           grind)
        | exact superpose b0e867 b0e11
        | exact resolve b0e11 b0e867
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e867
      have b0e1060 : y = (M.op y (M.op y x)) := by
        first
        | (have i₁ := b0e920 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e920
        | exact resolve b0e920 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1066 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e920 X0 (M.op X0 X0)
           have i₂ := b0e920 X0 X0
           grind)
        | exact superpose b0e920 b0e920
        | exact resolve b0e920 b0e920
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1187 : x = (M.op x y) := by
        first
        | (have i₁ := b0e920 y x
           have i₂ := b0e1060
           grind)
        | exact superpose b0e1060 b0e920
        | exact resolve b0e920 b0e1060
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e920 b0e1060
      have b0e2949 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e1066 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e1066
        | exact resolve b0e1066 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1066
      have b0e3301 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e2949
           grind)
        | exact superpose b0e2949 b0e18
        | exact resolve b0e18 b0e2949
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2949
      have b0e3313 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e3301
           have i₂ := b0e1187
           grind)
        | exact superpose b0e1187 b0e3301
        | exact resolve b0e3301 b0e1187
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1187 b0e3301
      have b0e3314 : False := by grind
      exact b0e3314
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : x = (k x y) := by grind
        have b1e75 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
        have b1e88 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e75
             have r₂ := b1e21
             grind)
          | exact resolve b1e75 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e89 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e88
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e88
          | exact resolve b1e88 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e90 : (σ x) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e89
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e89
          | exact resolve b1e89 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e89
        have b1e91 : False := by grind
        exact b1e91
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : x = (k x y) := by grind
        have b2e28 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b2e12 y X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
             have i₂ := b2e12 X0 X2 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (σ y)
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 (M.op (σ y) (σ y)) x
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ y) (σ x)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e70 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b2e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e246 : (σ y) = (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e43 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e247 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e246
             have r₂ := b2e22
             grind)
          | exact resolve b2e246 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e246
        have b2e248 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e247
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e247
          | exact resolve b2e247 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e247
        have b2e249 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e248
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e248
          | exact resolve b2e248 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e248
        have b2e497 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X2 X0 X1
             have i₂ := b2e12 X0 X0 X1
             grind)
          | exact superpose b2e12 b2e29
          | exact resolve b2e29 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29
        have b2e545 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X1 x
             have i₂ := b2e497 X1 x X0
             grind)
          | exact superpose b2e497 b2e12
          | exact resolve b2e12 b2e497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e497
        have b2e677 : (σ x) = (M.op (σ x) (M.op (σ y) (σ x))) := by
          first
          | (have i₁ := b2e545 (σ y) (σ x)
             have i₂ := b2e249
             grind)
          | exact superpose b2e249 b2e545
          | exact resolve b2e545 b2e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e679 : y = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b2e545 y y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e545
          | exact resolve b2e545 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e700 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e677
             have i₂ := b2e249
             grind)
          | exact superpose b2e249 b2e677
          | exact resolve b2e677 b2e249
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e249 b2e677
        have b2e808 : x = (M.op x y) := by
          first
          | (have i₁ := b2e545 y x
             have i₂ := b2e679
             grind)
          | exact superpose b2e679 b2e545
          | exact resolve b2e545 b2e679
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e679
        have b2e852 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b2e28 X0
             have i₂ := b2e808
             grind)
          | exact superpose b2e808 b2e28
          | exact resolve b2e28 b2e808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e808
        have b2e1805 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e700
             grind)
          | exact superpose b2e700 b2e22
          | exact resolve b2e22 b2e700
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1810 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b2e700
        have b2e1832 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e1810
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e1810
          | exact resolve b2e1810 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1810
        have b2e2355 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b2e13 (k x x)
             have i₂ := b2e1832
             grind)
          | exact superpose b2e1832 b2e13
          | exact resolve b2e13 b2e1832
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1832
        have b2e2373 : x = (k x x) := by
          first
          | (have i₁ := b2e2355
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e2355
          | exact resolve b2e2355 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2355
        have b2e2656 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e70 x x
             have i₂ := b2e2373
             grind)
          | exact superpose b2e2373 b2e70
          | (have j0 := b2e70 x x
             grind)
          | exact resolve b2e70 b2e2373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70 b2e2373
        have b2e2657 : x = (M.op x x) := by grind
        clear b2e2656
        have b2e2980 : x = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b2e545 x x
             have i₂ := b2e2657
             grind)
          | exact superpose b2e2657 b2e545
          | exact resolve b2e545 b2e2657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e545 b2e2657
        have b2e2981 : x = y := by
          first
          | (have i₁ := b2e2980
             have i₂ := b2e852 x
             grind)
          | exact superpose b2e852 b2e2980
          | exact resolve b2e2980 b2e852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e852 b2e2980
        have b2e3580 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1805
             have i₂ := b2e2981
             grind)
          | exact superpose b2e2981 b2e1805
          | exact resolve b2e1805 b2e2981
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1805 b2e2981
        have b2e3584 : False := by grind
        exact b2e3584
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
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
        have b3e32 : (k x y) = (τ (σ x)) := by
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
        have b3e33 : x = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e74 : (M.op y y) = (k x y) ∨ x = (M.op y y) := by grind
        have b3e84 : (M.op y y) = (k x y) := by
          first
          | (have r₁ := b3e74
             have r₂ := b3e20
             grind)
          | exact resolve b3e74 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74
        have b3e86 : x = (M.op y y) := by
          first
          | (have i₁ := b3e84
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e84
          | exact resolve b3e84 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e84
        have b3e89 : False := by grind
        exact b3e89
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e36 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ x)))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b4e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 : G, (M.op y x) = (M.op (M.op X0 (M.op y x)) x) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op y x) (M.op X0 (M.op y x)) X0
               have i₂ := b4e36 (M.op X0 (M.op y x))
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
          have b4e79 : (M.op y y) = (k x y) ∨ x = (M.op y y) := by grind
          have b4e89 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b4e79
               have r₂ := b4e21
               grind)
            | exact resolve b4e79 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e90 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e78
               have r₂ := b4e23
               grind)
            | exact resolve b4e78 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e91 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e90
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e90
            | exact resolve b4e90 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90
          have b4e92 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e91
               have i₂ := b4e89
               grind)
            | exact superpose b4e89 b4e91
            | exact resolve b4e91 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e91
          have b4e127 : ∀ X0 : G, (M.op (σ (M.op y y)) (σ y)) = (M.op (M.op X0 (M.op (σ (M.op y y)) (σ y))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e39 (σ y) x (σ y)
               have i₂ := b4e92
               grind)
            | exact superpose b4e92 b4e39
            | exact resolve b4e39 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 : G, (M.op (M.op X0 (M.op y x)) (M.op y x)) = (M.op x (M.op y x)) := by
            intro X0
            first
            | (have i₁ := b4e39 (M.op y x) (M.op X0 (M.op y x)) X0
               have i₂ := b4e36 (M.op X0 (M.op y x))
               grind)
            | exact superpose b4e36 b4e39
            | exact resolve b4e39 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e877 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 X0 X2 X0 X1
               have i₂ := b4e13 X0 X0 X1
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e920 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op y x)) (M.op y x)) = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e877 x X0 (M.op X1 (M.op y x))
               have i₂ := b4e40 X1
               grind)
            | exact superpose b4e40 b4e877
            | exact resolve b4e877 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e929 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X1 x
               have i₂ := b4e877 X1 x X0
               grind)
            | exact superpose b4e877 b4e13
            | exact resolve b4e13 b4e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e957 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b4e920 X0 x
               have i₂ := b4e130 x
               grind)
            | exact superpose b4e130 b4e920
            | exact resolve b4e920 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130 b4e920
          have b4e1071 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e929 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e929
            | exact resolve b4e929 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1077 : (M.op y x) = (M.op (M.op y x) x) := by
            first
            | (have i₁ := b4e929 x (M.op y x)
               have i₂ := b4e36 x
               grind)
            | exact superpose b4e36 b4e929
            | exact resolve b4e929 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e1078 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b4e929 X0 (M.op X0 X0)
               have i₂ := b4e929 X0 X0
               grind)
            | exact superpose b4e929 b4e929
            | exact resolve b4e929 b4e929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1199 : y = (M.op y x) := by
            first
            | (have i₁ := b4e929 x y
               have i₂ := b4e1071
               grind)
            | exact superpose b4e1071 b4e929
            | exact resolve b4e929 b4e1071
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e929 b4e1071
          have b4e2358 : ∀ X0 : G, (M.op (M.op y x) (M.op y x)) = (M.op x (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b4e877 x X0 (M.op y x)
               have i₂ := b4e1077
               grind)
            | exact superpose b4e1077 b4e877
            | exact resolve b4e877 b4e1077
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e877 b4e1077
          have b4e2362 : (M.op (M.op y x) (M.op y x)) = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e2358 x
               have i₂ := b4e957 x
               grind)
            | exact superpose b4e957 b4e2358
            | exact resolve b4e2358 b4e957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e957 b4e2358
          have b4e2363 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e2362
               have i₂ := b4e1199
               grind)
            | exact superpose b4e1199 b4e2362
            | exact resolve b4e2362 b4e1199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1199 b4e2362
          have b4e3639 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e1078 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e1078
            | exact resolve b4e1078 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3640 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b4e1078 (σ y)
               have i₂ := b4e92
               grind)
            | exact superpose b4e92 b4e1078
            | exact resolve b4e1078 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92 b4e1078
          have b4e3689 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e3640
               have i₂ := b4e2363
               grind)
            | exact superpose b4e2363 b4e3640
            | exact resolve b4e3640 b4e2363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3640
          have b4e4276 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e3639
               grind)
            | exact superpose b4e3639 b4e37
            | exact resolve b4e37 b4e3639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e3639
          have b4e8298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b4e127 (σ (M.op y y))
               have i₂ := b4e4276 (σ (M.op y y))
               grind)
            | exact superpose b4e4276 b4e127
            | exact resolve b4e127 b4e4276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127 b4e4276
          have b4e8376 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
            first
            | (have i₁ := b4e8298
               have i₂ := b4e2363
               grind)
            | exact superpose b4e2363 b4e8298
            | exact resolve b4e8298 b4e2363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2363 b4e8298
          have b4e8408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e8376
               have i₂ := b4e3689
               grind)
            | exact superpose b4e3689 b4e8376
            | exact resolve b4e8376 b4e3689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3689 b4e8376
          have b4e8438 : False := by grind
          exact b4e8438
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : y = (k y x) := by grind
          have b5e34 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ x)
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e82 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e71 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e247 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b5e50 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e248 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b5e247
               have r₂ := b5e23
               grind)
            | exact resolve b5e247 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e247
          have b5e249 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b5e248
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e248
            | exact resolve b5e248 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248
          have b5e250 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e249
               have i₂ := b5e27
               grind)
            | exact superpose b5e27 b5e249
            | exact resolve b5e249 b5e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e249
          have b5e482 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 X0 X2 X0 X1
               have i₂ := b5e13 X0 X0 X1
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e530 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X1 x
               have i₂ := b5e482 X1 x X0
               grind)
            | exact superpose b5e482 b5e13
            | exact resolve b5e13 b5e482
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e482
          have b5e664 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e530 (σ x) (σ y)
               have i₂ := b5e250
               grind)
            | exact superpose b5e250 b5e530
            | exact resolve b5e530 b5e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e665 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b5e530 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e530
            | exact resolve b5e530 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e686 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e664
               have i₂ := b5e250
               grind)
            | exact superpose b5e250 b5e664
            | exact resolve b5e664 b5e250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e250 b5e664
          have b5e796 : y = (M.op y x) := by
            first
            | (have i₁ := b5e530 x y
               have i₂ := b5e665
               grind)
            | exact superpose b5e665 b5e530
            | exact resolve b5e530 b5e665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e530 b5e665
          have b5e842 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b5e34 X0
               have i₂ := b5e796
               grind)
            | exact superpose b5e796 b5e34
            | exact resolve b5e34 b5e796
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e796
          have b5e1788 : (σ y) = (k (σ y) (σ y)) := by grind
          clear b5e686
          have b5e1810 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b5e1788
               have i₂ := b5e19 y y
               grind)
            | exact superpose b5e19 b5e1788
            | exact resolve b5e1788 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1788
          have b5e2345 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y y)
               have i₂ := b5e1810
               grind)
            | exact superpose b5e1810 b5e14
            | exact resolve b5e14 b5e1810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1810
          have b5e2363 : y = (k y y) := by
            first
            | (have i₁ := b5e2345
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e2345
            | exact resolve b5e2345 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2345
          have b5e2646 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e82 y y
               have i₂ := b5e2363
               grind)
            | exact superpose b5e2363 b5e82
            | (have j0 := b5e82 y y
               grind)
            | exact resolve b5e82 b5e2363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e2363
          have b5e2647 : y = (M.op y y) := by grind
          clear b5e2646
          have b5e2989 : x = (M.op y y) := by
            first
            | (have i₁ := b5e842 y
               have i₂ := b5e2647
               grind)
            | exact superpose b5e2647 b5e842
            | exact resolve b5e842 b5e2647
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e842 b5e2647
          have b5e3031 : False := by grind
          exact b5e3031
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ x) = (k (σ x) (σ y)) := by grind
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
        have b6e27 : (k x y) = (τ (σ x)) := by
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
        have b6e28 : x = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e40 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
             have i₂ := b6e12 X0 X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
        have b6e70 : x = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e28
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e28 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e73 : x = (M.op y x) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e70
             have r₂ := b6e20
             grind)
          | exact resolve b6e70 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e70
        have b6e76 : x = (M.op y x) := by
          first
          | (have r₁ := b6e73
             have r₂ := b6e21
             grind)
          | exact resolve b6e73 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e79 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e91 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b6e79 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e755 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e40 X0 X2 X0 X1
             have i₂ := b6e12 X0 X0 X1
             grind)
          | exact superpose b6e12 b6e40
          | exact resolve b6e40 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e806 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X1 x
             have i₂ := b6e755 X1 x X0
             grind)
          | exact superpose b6e755 b6e12
          | exact resolve b6e12 b6e755
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e755
        have b6e944 : x = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b6e806 y x
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e806
          | exact resolve b6e806 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e806
        have b6e964 : x = (M.op x x) := by
          first
          | (have i₁ := b6e944
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e944
          | exact resolve b6e944 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76 b6e944
        have b6e1078 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e964
             grind)
          | exact superpose b6e964 b6e21
          | exact resolve b6e21 b6e964
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e964
        have b6e1140 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e68 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e68
          | exact resolve b6e68 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e1347 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e1140
        have b6e5665 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e1347
             grind)
          | exact superpose b6e1347 b6e13
          | exact resolve b6e13 b6e1347
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5691 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5665
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e5665
          | exact resolve b6e5665 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5665
        have b6e5810 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e91 y y
             have i₂ := b6e5691
             grind)
          | exact superpose b6e5691 b6e91
          | (have j0 := b6e91 y x
             grind)
          | exact resolve b6e91 b6e5691
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e91 b6e5691
        have b6e5811 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e5810
        have b6e5817 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e5811
             have r₂ := b6e20
             grind)
          | exact resolve b6e5811 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5811
        have b6e5961 : y = (k y y) ∨ (σ x) = (σ y) := by grind
        clear b6e5817
        have b6e6123 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1347
             have i₂ := b6e5961
             grind)
          | exact superpose b6e5961 b6e1347
          | exact resolve b6e1347 b6e5961
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1347 b6e5961
        have b6e6148 : (σ x) = (σ y) := by grind
        clear b6e6123
        have b6e6208 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e6148
             grind)
          | exact superpose b6e6148 b6e13
          | exact resolve b6e13 b6e6148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6148
        have b6e6241 : x = y := by
          first
          | (have i₁ := b6e6208
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e6208
          | exact resolve b6e6208 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6208
        have b6e6248 : False := by grind
        exact b6e6248
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ y) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e34 : y = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b7e13 X0 X2 X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e62 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b7e64 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 y x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 y x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : y = (M.op x y) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e70 : y = (M.op x y) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e21
               grind)
            | exact resolve b7e67 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e74 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e76 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
          have b7e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e74 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e86 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e23
               grind)
            | exact resolve b7e76 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e87 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e86
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e86
            | exact resolve b7e86 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e474 : y = (M.op x x) ∨ (k x y) = (M.op y x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e84 x y
               grind)
            | exact superpose b7e84 b7e34
            | (have j1 := b7e84 x y
               grind)
            | exact resolve b7e34 b7e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e84
          have b7e481 : y = (M.op x x) ∨ (k x y) = (M.op y x) := by grind
          clear b7e474
          have b7e499 : (k x y) = (M.op y x) := by
            first
            | (have r₁ := b7e481
               have r₂ := b7e22
               grind)
            | exact resolve b7e481 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e481
          have b7e680 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e38 X0 X2 X0 X1
               have i₂ := b7e13 X0 X0 X1
               grind)
            | exact superpose b7e13 b7e38
            | exact resolve b7e38 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e731 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X1 x
               have i₂ := b7e680 X1 x X0
               grind)
            | exact superpose b7e680 b7e13
            | exact resolve b7e13 b7e680
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e680
          have b7e868 : y = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e731 x y
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e731
            | exact resolve b7e731 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e888 : y = (M.op y y) := by
            first
            | (have i₁ := b7e868
               have i₂ := b7e70
               grind)
            | exact superpose b7e70 b7e868
            | exact resolve b7e868 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e868
          have b7e1001 : x ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e888
               grind)
            | exact superpose b7e888 b7e21
            | exact resolve b7e21 b7e888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1002 : y = (k y y) := by grind
          have b7e1067 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e62 y y
               have i₂ := b7e87
               grind)
            | exact superpose b7e87 b7e62
            | exact resolve b7e62 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62 b7e87
          have b7e1278 : (σ (k x y)) = (σ (k y y)) ∨ (σ y) = (σ (k x y)) := by grind
          clear b7e1067
          have b7e1341 : (σ y) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1278
               have i₂ := b7e1002
               grind)
            | exact superpose b7e1002 b7e1278
            | exact resolve b7e1278 b7e1002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1002 b7e1278
          have b7e1342 : (σ y) = (σ (k x y)) := by grind
          clear b7e1341
          have b7e1376 : (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b7e1342
               have i₂ := b7e499
               grind)
            | exact superpose b7e499 b7e1342
            | exact resolve b7e1342 b7e499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e499 b7e1342
          have b7e1551 : (τ (σ y)) = (M.op y x) := by
            first
            | (have i₁ := b7e14 (M.op y x)
               have i₂ := b7e1376
               grind)
            | exact superpose b7e1376 b7e14
            | exact resolve b7e14 b7e1376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1376
          have b7e1568 : y = (M.op y x) := by
            first
            | (have i₁ := b7e1551
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1551
            | exact resolve b7e1551 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1551
          have b7e1786 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e731 y x
               have i₂ := b7e1568
               grind)
            | exact superpose b7e1568 b7e731
            | exact resolve b7e731 b7e1568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e731 b7e1568
          have b7e1787 : x = (M.op x y) := by
            first
            | (have i₁ := b7e1786
               have i₂ := b7e888
               grind)
            | exact superpose b7e888 b7e1786
            | exact resolve b7e1786 b7e888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e888 b7e1786
          have b7e2269 : x = y := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e1787
               grind)
            | exact superpose b7e1787 b7e70
            | exact resolve b7e70 b7e1787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e1787
          have b7e2281 : False := by grind
          exact b7e2281
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e44 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ x)
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 (M.op (σ x) (σ x)) x
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ x)
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
          have b8e279 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e44 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e280 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e279
               have r₂ := b8e23
               grind)
            | exact resolve b8e279 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e279
          have b8e281 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e280
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e280
            | exact resolve b8e280 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e280
          have b8e282 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e281
               grind)
            | exact superpose b8e281 b8e20
            | exact resolve b8e20 b8e281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e281
          have b8e291 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e282
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e282
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e282 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e282
          have b8e292 : y = (M.op x x) ∨ x = (M.op y y) := by grind
          clear b8e291
          have b8e295 : x = (M.op y y) := by
            first
            | (have r₁ := b8e292
               have r₂ := b8e22
               grind)
            | exact resolve b8e292 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e292
          have b8e299 : False := by grind
          exact b8e299

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_y_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e60 : False := by grind
      exact b0e60
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
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
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b5e13 X0 X2 X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b5e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e40 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40
            | exact resolve b5e40 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e46 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e49 : x = y ∨ y = (k x y) := by grind
          clear b5e46
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e79 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e82 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op y x) := by
            intro X0
            first
            | (have i₁ := b5e42 x (M.op X0 x) X0
               have i₂ := b5e43 (M.op X0 x)
               grind)
            | exact superpose b5e43 b5e42
            | exact resolve b5e42 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e94 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b5e13 x X0 x
               have i₂ := b5e82 x
               grind)
            | exact superpose b5e82 b5e13
            | exact resolve b5e13 b5e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e113 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41 X0 X2 X0 X1
               have i₂ := b5e13 X0 X0 X1
               grind)
            | exact superpose b5e13 b5e41
            | exact resolve b5e41 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e129 : x = (M.op y y) := by
            first
            | (have i₁ := b5e94 y
               have i₂ := b5e43 y
               grind)
            | exact superpose b5e43 b5e94
            | exact resolve b5e94 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e94
          have b5e157 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X2 (M.op X2 (M.op (σ (k X0 X1)) (σ X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e53 X1 X0
               grind)
            | exact superpose b5e53 b5e13
            | (have j1 := b5e53 X1 X0
               grind)
            | exact resolve b5e13 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e303 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X1 x
               have i₂ := b5e113 X1 x X0
               grind)
            | exact superpose b5e113 b5e13
            | exact resolve b5e13 b5e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113
          have b5e552 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e303 X0 (M.op X0 X0)
               have i₂ := b5e303 X0 X0
               grind)
            | exact superpose b5e303 b5e303
            | exact resolve b5e303 b5e303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e303
          have b5e753 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e552 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e552
            | exact resolve b5e552 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e552
          have b5e2084 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e157 x y X0
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e157
            | (have j0 := b5e157 x y x
               grind)
            | exact resolve b5e157 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157
          have b5e2137 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e2084 X0
               grind)
            | (have r₁ := b5e2084 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2084 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2084
          have b5e2142 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ x)))) := by
            intro X0
            first
            | (have j0 := b5e2137 X0
               grind)
            | (have r₁ := b5e2137 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2137 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2137
          have b5e10001 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ (k x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e2142 X0
               have i₂ := b5e53 y x
               grind)
            | exact superpose b5e53 b5e2142
            | (have j1 := b5e53 y x
               grind)
            | exact resolve b5e2142 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53 b5e2142
          have b5e10090 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ (k x y)))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e10001 X0
               grind)
            | (have r₁ := b5e10001 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e10001 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10001
          have b5e10110 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ (k x y)))) := by
            intro X0
            first
            | (have j0 := b5e10090 X0
               grind)
            | (have r₁ := b5e10090 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e10090 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10090
          have b5e10120 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e10110 X0
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e10110
            | exact resolve b5e10110 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e10110
          have b5e10181 : (M.op (σ x) (σ y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b5e79 y (σ (M.op y y))
               have i₂ := b5e10120 (σ (M.op y y))
               grind)
            | exact superpose b5e10120 b5e79
            | exact resolve b5e79 b5e10120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79 b5e10120
          have b5e10227 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e10181
               have i₂ := b5e753 y
               grind)
            | exact superpose b5e753 b5e10181
            | exact resolve b5e10181 b5e753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e753 b5e10181
          have b5e10258 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e10227
               have i₂ := b5e129
               grind)
            | exact superpose b5e129 b5e10227
            | exact resolve b5e10227 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129 b5e10227
          have b5e10281 : False := by grind
          exact b5e10281
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
          have b7e33 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
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
          have b7e35 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b7e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (σ x))) := by
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
          have b7e42 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e39
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e44 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e43
            | exact resolve b7e43 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e47 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e14
            | exact resolve b7e14 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : y = (k x y) := by
            first
            | (have i₁ := b7e47
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e47
            | exact resolve b7e47 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e57 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e58 : y = (M.op y x) ∨ x = y := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e22
               grind)
            | exact resolve b7e57 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e60 : y = (M.op y x) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e21
               grind)
            | exact resolve b7e58 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58
          have b7e71 : ∀ X0 : G, x = (M.op X0 (M.op X0 (M.op y x))) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e13
            | exact resolve b7e13 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, x = (M.op X0 (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e71 X0
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e71
            | exact resolve b7e71 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60 b7e71
          have b7e93 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e36 (σ x)
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e36
            | exact resolve b7e36 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e36
          have b7e120 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b7e35 y (M.op X0 y) X0
               have i₂ := b7e73 (M.op X0 y)
               grind)
            | exact superpose b7e73 b7e35
            | exact resolve b7e35 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e227 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
            intro X0
            first
            | (have i₁ := b7e13 y X0 x
               have i₂ := b7e120 x
               grind)
            | exact superpose b7e120 b7e13
            | exact resolve b7e13 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120
          have b7e245 : y = (M.op x x) := by
            first
            | (have i₁ := b7e227 x
               have i₂ := b7e73 x
               grind)
            | exact superpose b7e73 b7e227
            | exact resolve b7e227 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e227
          have b7e323 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e245
               grind)
            | exact superpose b7e245 b7e93
            | exact resolve b7e93 b7e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e245
          have b7e331 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e323
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e323
            | exact resolve b7e323 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e323
          have b7e335 : False := by grind
          exact b7e335
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
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
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b8e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e60 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e61 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X1 (M.op (M.op X2 X0) X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e33 (M.op X1 (M.op (M.op X2 X0) X0)) X1 X1
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (M.op (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 (σ X0) X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e33
            | exact resolve b8e33 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e64 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
               have i₂ := b8e13 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
               grind)
            | exact superpose b8e13 b8e33
            | exact resolve b8e33 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op (M.op X1 X2) X2))) X1
               have i₂ := b8e33 (M.op (M.op X1 X2) X2) X3 X0
               grind)
            | exact superpose b8e33 b8e13
            | exact resolve b8e13 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X2 X0 X1
               have i₂ := b8e13 X0 X0 X1
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e137 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X0) (σ X1)
               have i₂ := b8e55 X1 X0
               grind)
            | exact superpose b8e55 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e55 X1 X0
               grind)
            | (have r₁ := b8e17 (σ X1) (σ X0)
               have r₂ := b8e55 X0 X1
               grind)
            | exact resolve b8e17 b8e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e55
          have b8e140 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e137 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137
          have b8e141 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e140 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e140
          have b8e145 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e141 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e141
            | (have j0 := b8e141 X0 X1
               grind)
            | exact resolve b8e141 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e204 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e89 X1 x X3
               have i₂ := b8e89 X1 x X0
               grind)
            | exact superpose b8e89 b8e89
            | exact resolve b8e89 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e213 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X1 x
               have i₂ := b8e89 X1 x X0
               grind)
            | exact superpose b8e89 b8e13
            | exact resolve b8e13 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e219 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 X0 (M.op X2 X0) X2
               have i₂ := b8e89 X0 X1 (M.op X2 X0)
               grind)
            | exact superpose b8e89 b8e33
            | exact resolve b8e33 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e229 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e219 X0 X1 X2
               have i₂ := b8e33 X0 X0 X1
               grind)
            | exact superpose b8e33 b8e219
            | exact resolve b8e219 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e246 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
            intro X0
            first
            | (have i₁ := b8e213 X0 (M.op X0 X0)
               have i₂ := b8e213 X0 X0
               grind)
            | exact superpose b8e213 b8e213
            | exact resolve b8e213 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e253 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e33 (M.op X0 (M.op X0 X1)) X1 X1
               have i₂ := b8e213 X0 X1
               grind)
            | exact superpose b8e213 b8e33
            | exact resolve b8e33 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e257 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e253 X1 X0 X2
               have i₂ := b8e213 X0 X1
               grind)
            | exact superpose b8e213 b8e253
            | exact resolve b8e253 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e271 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e60 X0 (σ (M.op X0 X0))
               have i₂ := b8e89 (σ X0) X1 (σ (M.op X0 X0))
               grind)
            | exact superpose b8e89 b8e60
            | exact resolve b8e60 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e295 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e246 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e246
            | exact resolve b8e246 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e298 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 X0 X1 X0
               have i₂ := b8e246 X0
               grind)
            | exact superpose b8e246 b8e33
            | exact resolve b8e33 b8e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e299 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 X0
               have i₂ := b8e246 X0
               grind)
            | exact superpose b8e246 b8e13
            | exact resolve b8e13 b8e246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e213 X1 (M.op X1 (M.op X0 X0))
               have i₂ := b8e299 X0 X1
               grind)
            | exact superpose b8e299 b8e213
            | exact resolve b8e213 b8e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e469 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e204 X1 (M.op X2 (M.op X0 X0)) X2
               have i₂ := b8e299 X0 X2
               grind)
            | exact superpose b8e299 b8e204
            | exact resolve b8e204 b8e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e470 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (M.op X1 (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e204 X1 (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0))) X2
               have i₂ := b8e60 X0 X2
               grind)
            | exact superpose b8e60 b8e204
            | exact resolve b8e204 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e471 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e204 X1 (M.op X2 (M.op X2 X0)) X0
               have i₂ := b8e213 X2 X0
               grind)
            | exact superpose b8e213 b8e204
            | exact resolve b8e204 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e536 : ∀ X0 X1 X2 : G, (M.op X2 (σ X0)) = (M.op X1 (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e470 X0 X1 X2
               have i₂ := b8e295 X0
               grind)
            | exact superpose b8e295 b8e470
            | exact resolve b8e470 b8e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e470
          have b8e601 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X2 (M.op X2 X0))) (M.op X2 (M.op X2 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e229 (M.op X2 (M.op X2 X0)) X0 X1
               have i₂ := b8e213 X2 X0
               grind)
            | exact superpose b8e213 b8e229
            | exact resolve b8e229 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e641 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e246 X1
               have i₂ := b8e229 X1 X0 X1
               grind)
            | (have i₁ := b8e246 X1
               have i₂ := b8e229 X1 X1 X0
               grind)
            | exact superpose b8e229 b8e246
            | exact resolve b8e246 b8e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e229 b8e246
          have b8e673 : ∀ X0 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) := by
            intro X0 X2
            first
            | (have i₁ := b8e601 X0 x X2
               have i₂ := b8e641 x (M.op X2 (M.op X2 X0))
               grind)
            | exact superpose b8e641 b8e601
            | exact resolve b8e601 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e601
          have b8e703 : ∀ X0 X2 : G, (M.op (M.op X2 (M.op X2 X0)) (M.op X2 (M.op X2 X0))) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b8e673 X0 X2
               have i₂ := b8e213 X2 X0
               grind)
            | exact superpose b8e213 b8e673
            | exact resolve b8e673 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e673
          have b8e876 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e257 (M.op X1 (M.op X0 X0)) X2 X1
               have i₂ := b8e299 X0 X1
               grind)
            | exact superpose b8e299 b8e257
            | exact resolve b8e257 b8e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e299
          have b8e877 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) = (M.op (σ X0) (M.op X2 (M.op X2 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e257 (M.op X1 (M.op (σ (M.op X0 X0)) (σ X0))) X2 X1
               have i₂ := b8e60 X0 X1
               grind)
            | exact superpose b8e60 b8e257
            | exact resolve b8e257 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60 b8e257
          have b8e964 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op X2 (M.op X2 (M.op X1 (σ (M.op X0 X0)))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e877 X0 X1 X2
               have i₂ := b8e295 X0
               grind)
            | exact superpose b8e295 b8e877
            | exact resolve b8e877 b8e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e877
          have b8e965 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e876 X0 X1 x
               have i₂ := b8e469 X0 x X1
               grind)
            | exact superpose b8e469 b8e876
            | exact resolve b8e876 b8e469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e876
          have b8e970 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op (σ X0) (M.op X1 (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e964 X0 X1 x
               have i₂ := b8e536 X0 x X1
               grind)
            | exact superpose b8e536 b8e964
            | exact resolve b8e964 b8e536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e536 b8e964
          have b8e1024 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e298 X1 X1
               have i₂ := b8e204 X1 X1 X0
               grind)
            | (have i₁ := b8e298 X1 X1
               have i₂ := b8e204 X0 X1 X1
               grind)
            | exact superpose b8e204 b8e298
            | exact resolve b8e298 b8e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e298
          have b8e1209 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (M.op (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0))) (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e89 (σ X0) X1 (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0)))
               have i₂ := b8e62 X0 X2
               grind)
            | exact superpose b8e62 b8e89
            | exact resolve b8e89 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62 b8e89
          have b8e1224 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ (M.op X0 X0)) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1209 X0 X1 x
               have i₂ := b8e641 x (M.op (σ (M.op X0 X0)) (σ X0))
               grind)
            | exact superpose b8e641 b8e1209
            | exact resolve b8e1209 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1209
          have b8e1243 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1224 X0 X1
               have i₂ := b8e295 X0
               grind)
            | exact superpose b8e295 b8e1224
            | exact resolve b8e1224 b8e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e295 b8e1224
          have b8e1255 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1243 X0 X1
               have i₂ := b8e30 (M.op X0 X0)
               grind)
            | exact superpose b8e30 b8e1243
            | exact resolve b8e1243 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e1243
          have b8e1264 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (σ (M.op X0 (M.op (M.op X0 X0) X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1255 X0 X1
               have i₂ := b8e965 X0 (M.op X0 X0)
               grind)
            | exact superpose b8e965 b8e1255
            | exact resolve b8e1255 b8e965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1255
          have b8e1271 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1264 X0 X1
               have i₂ := b8e641 X0 X0
               grind)
            | exact superpose b8e641 b8e1264
            | exact resolve b8e1264 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1264
          have b8e1275 : ∀ X0 X1 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1271 X0 X1
               have i₂ := b8e970 X0 (M.op X1 (σ X0))
               grind)
            | exact superpose b8e970 b8e1271
            | exact resolve b8e1271 b8e970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1271
          have b8e1816 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e145 y x
               grind)
            | exact superpose b8e145 b8e20
            | (have j1 := b8e145 x y
               grind)
            | exact resolve b8e20 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145
          have b8e1850 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have r₁ := b8e1816
               have r₂ := b8e23
               grind)
            | exact resolve b8e1816 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1816
          have b8e1950 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 X1))) = (M.op X2 (M.op X2 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e204 X2 (M.op X0 X1) X1
               have i₂ := b8e965 X1 X0
               grind)
            | (have i₁ := b8e204 X0 (M.op X0 X0) X1
               have i₂ := b8e965 X0 X1
               grind)
            | exact superpose b8e965 b8e204
            | exact resolve b8e204 b8e965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1956 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e641 X1 (M.op X0 X1)
               have i₂ := b8e965 X1 X0
               grind)
            | (have i₁ := b8e641 X1 (M.op X0 X0)
               have i₂ := b8e965 X0 X1
               grind)
            | exact superpose b8e965 b8e641
            | exact resolve b8e641 b8e965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1963 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1956 X0 X1
               have i₂ := b8e358 X1 X0
               grind)
            | exact superpose b8e358 b8e1956
            | exact resolve b8e1956 b8e358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358 b8e1956
          have b8e3846 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1024 X0 (M.op X1 (M.op (M.op X2 X0) X0))
               have i₂ := b8e61 X0 X1 X2 X0
               grind)
            | exact superpose b8e61 b8e1024
            | exact resolve b8e1024 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1024
          have b8e3866 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e204 X3 (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X4 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))))
               have i₂ := b8e61 X0 X1 X2 X4
               grind)
            | exact superpose b8e61 b8e204
            | exact resolve b8e204 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e3883 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3866 X0 X1 X2 X3 x
               have i₂ := b8e641 x (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0)))
               grind)
            | exact superpose b8e641 b8e3866
            | exact resolve b8e3866 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3866
          have b8e3892 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3846 X0 X1 X2
               have i₂ := b8e1963 X1 (M.op (M.op X2 X0) X0)
               grind)
            | exact superpose b8e1963 b8e3846
            | exact resolve b8e3846 b8e1963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3846
          have b8e3930 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X1 (M.op (M.op X2 X0) X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3883 X0 X1 X2 X3
               have i₂ := b8e1963 X0 (M.op X1 (M.op (M.op X2 X0) X0))
               grind)
            | exact superpose b8e1963 b8e3883
            | exact resolve b8e3883 b8e1963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3883
          have b8e3939 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3892 X0 X1 X2
               have i₂ := b8e1963 (M.op X2 X0) X0
               grind)
            | exact superpose b8e1963 b8e3892
            | exact resolve b8e3892 b8e1963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3892
          have b8e3959 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X0 (M.op X1 (M.op (M.op (M.op X2 X0) X0) (M.op (M.op X2 X0) X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3930 X0 X1 X2 X3
               have i₂ := b8e1963 X1 (M.op (M.op X2 X0) X0)
               grind)
            | exact superpose b8e1963 b8e3930
            | exact resolve b8e3930 b8e1963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3930
          have b8e3966 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = (M.op X1 (M.op X0 (M.op (M.op X2 X0) X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e3939 X0 X1 X2
               have i₂ := b8e965 X0 (M.op X2 X0)
               grind)
            | exact superpose b8e965 b8e3939
            | exact resolve b8e3939 b8e965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3939
          have b8e3979 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X0 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3959 X0 X1 X2 X3
               have i₂ := b8e1963 (M.op X2 X0) X0
               grind)
            | exact superpose b8e1963 b8e3959
            | exact resolve b8e3959 b8e1963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1963 b8e3959
          have b8e3985 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 X0))) = (M.op X1 (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e3966 X1 X1 X0
               have i₂ := b8e641 X0 X1
               grind)
            | exact superpose b8e641 b8e3966
            | exact resolve b8e3966 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3966
          have b8e3997 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 (M.op (M.op X2 X0) X0)))) = (M.op X0 (M.op X1 (M.op X0 (M.op (M.op X2 X0) X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e3979 X0 X1 X2 X3
               have i₂ := b8e965 X0 (M.op X2 X0)
               grind)
            | exact superpose b8e965 b8e3979
            | exact resolve b8e3979 b8e965
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e965 b8e3979
          have b8e4008 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) = (M.op X3 (M.op X3 (M.op X1 (M.op X0 X0)))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e3997 X1 X1 X0 X3
               have i₂ := b8e641 X0 X1
               grind)
            | exact superpose b8e641 b8e3997
            | exact resolve b8e3997 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3997
          have b8e4012 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e4008 X0 X1 x
               have i₂ := b8e469 X0 x X1
               grind)
            | exact superpose b8e469 b8e4008
            | exact resolve b8e4008 b8e469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e469 b8e4008
          have b8e4365 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op (M.op X3 X0) X0))) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X3 X0) X0) (M.op X1 (M.op (M.op X2 (M.op (M.op X3 X0) X0)) (M.op (M.op X3 X0) X0))) X2
               have i₂ := b8e68 X2 X3 X0 X1
               grind)
            | exact superpose b8e68 b8e13
            | exact resolve b8e13 b8e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e4404 : ∀ X0 X1 X3 : G, (M.op (M.op X3 X0) X0) = (M.op (M.op X1 (M.op X0 (M.op (M.op X3 X0) X0))) X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e4365 X0 X1 x X3
               have i₂ := b8e64 X0 x X3
               grind)
            | exact superpose b8e64 b8e4365
            | exact resolve b8e4365 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e4365
          have b8e4491 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 (M.op X0 X0))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e4404 X1 X1 X0
               have i₂ := b8e641 X0 X1
               grind)
            | exact superpose b8e641 b8e4404
            | exact resolve b8e4404 b8e641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e641 b8e4404
          have b8e10598 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e471 X2 X1 X1
               have i₂ := b8e204 X1 (M.op X1 X2) X0
               grind)
            | (have i₁ := b8e471 X2 X1 X1
               have i₂ := b8e204 X0 (M.op X1 X2) X1
               grind)
            | exact superpose b8e204 b8e471
            | exact resolve b8e471 b8e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10713 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e4491 (M.op X1 (M.op X1 X0)) X2
               have i₂ := b8e471 X0 (M.op X1 (M.op X1 X0)) X1
               grind)
            | exact superpose b8e471 b8e4491
            | exact resolve b8e4491 b8e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e471 b8e4491
          have b8e10809 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e10713 X0 X1 X2
               have i₂ := b8e703 X0 X1
               grind)
            | exact superpose b8e703 b8e10713
            | exact resolve b8e10713 b8e703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e703 b8e10713
          have b8e15291 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e4012 X1 X2
               have i₂ := b8e204 X1 X1 X0
               grind)
            | (have i₁ := b8e4012 X1 X2
               have i₂ := b8e204 X0 X1 X1
               grind)
            | exact superpose b8e204 b8e4012
            | exact resolve b8e4012 b8e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e204 b8e4012
          have b8e24907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e1850
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1850
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e1850
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e1850
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e1850 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1850
          have b8e24908 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by grind
          clear b8e24907
          have b8e24909 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b8e24908
               have r₂ := b8e21
               grind)
            | exact resolve b8e24908 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24908
          have b8e24910 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e14 (M.op x y)
               have i₂ := b8e24909
               grind)
            | exact superpose b8e24909 b8e14
            | exact resolve b8e14 b8e24909
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24909
          have b8e24996 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e24910
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e24910
            | exact resolve b8e24910 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24910
          have b8e25001 : y = (M.op y x) := by
            first
            | (have r₁ := b8e24996
               have r₂ := b8e22
               grind)
            | exact resolve b8e24996 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24996
          have b8e25049 : ∀ X0 : G, (M.op x x) = (M.op y (M.op X0 (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b8e10598 X0 y x
               have i₂ := b8e25001
               grind)
            | exact superpose b8e25001 b8e10598
            | exact resolve b8e10598 b8e25001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10598
          have b8e25051 : ∀ X0 : G, (M.op X0 x) = (M.op x (M.op X0 (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b8e15291 y x X0
               have i₂ := b8e25001
               grind)
            | exact superpose b8e25001 b8e15291
            | exact resolve b8e15291 b8e25001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15291
          have b8e25055 : y = (M.op x x) := by
            first
            | (have i₁ := b8e25049 x
               have i₂ := b8e213 x y
               grind)
            | exact superpose b8e213 b8e25049
            | exact resolve b8e25049 b8e213
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e213 b8e25049
          have b8e26192 : ∀ X0 : G, x = (M.op (M.op X0 y) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b8e10809 x x x
               have i₂ := b8e25055
               grind)
            | exact superpose b8e25055 b8e10809
            | exact resolve b8e10809 b8e25055
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10809 b8e25055
          have b8e41333 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))))) := by
            intro X0
            first
            | (have i₁ := b8e271 (M.op x y) X0
               have i₂ := b8e26192 x
               grind)
            | exact superpose b8e26192 b8e271
            | exact resolve b8e271 b8e26192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e271 b8e26192
          have b8e41473 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (M.op X0 (σ (M.op x y))) (σ (M.op (M.op x y) (M.op x y))))) := by
            intro X0
            first
            | (have i₁ := b8e41333 X0
               have i₂ := b8e970 (M.op x y) (M.op X0 (σ (M.op x y)))
               grind)
            | exact superpose b8e970 b8e41333
            | exact resolve b8e41333 b8e970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e970 b8e41333
          have b8e41522 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y))))) := by
            first
            | (have i₁ := b8e41473 x
               have i₂ := b8e1275 (M.op x y) x
               grind)
            | exact superpose b8e1275 b8e41473
            | exact resolve b8e41473 b8e1275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1275 b8e41473
          have b8e41558 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y (M.op x (M.op y y))))) := by
            first
            | (have i₁ := b8e41522
               have i₂ := b8e1950 x y (M.op x y)
               grind)
            | exact superpose b8e1950 b8e41522
            | exact resolve b8e41522 b8e1950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1950 b8e41522
          have b8e41578 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x (M.op y (M.op y y))))) := by
            first
            | (have i₁ := b8e41558
               have i₂ := b8e3985 y x
               grind)
            | exact superpose b8e3985 b8e41558
            | exact resolve b8e41558 b8e3985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3985 b8e41558
          have b8e41588 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op y x))) := by
            first
            | (have i₁ := b8e41578
               have i₂ := b8e25051 y
               grind)
            | exact superpose b8e25051 b8e41578
            | exact resolve b8e41578 b8e25051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25051 b8e41578
          have b8e41596 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e41588
               have i₂ := b8e25001
               grind)
            | exact superpose b8e25001 b8e41588
            | exact resolve b8e41588 b8e25001
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25001 b8e41588
          have b8e41601 : False := by grind
          exact b8e41601

/-- `Equation727`: `x = y ◇ (y ◇ ((z ◇ y) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation727 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law727 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law727.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
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
      have b0e58 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e60 : False := by grind
      exact b0e60
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
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e257 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e50 x y
               grind)
            | exact superpose b4e50 b4e20
            | (have j1 := b4e50 x y
               grind)
            | exact resolve b4e20 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b4e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e267 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e257
               have r₂ := b4e23
               grind)
            | exact resolve b4e257 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257
          have b4e1549 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e267
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e267
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e267
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e267
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e267 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e267
          have b4e1550 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b4e1549
          have b4e1551 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e1550
               have r₂ := b4e21
               grind)
            | exact resolve b4e1550 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1550
          have b4e3511 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1551
               grind)
            | exact superpose b4e1551 b4e20
            | exact resolve b4e20 b4e1551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3518 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e1551
               grind)
            | exact superpose b4e1551 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e1551
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e1551
               grind)
            | exact resolve b4e17 b4e1551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1551
          have b4e3536 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b4e3518
          have b4e3551 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e3536
               have r₂ := b4e23
               grind)
            | exact resolve b4e3536 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3536
          have b4e3560 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e3551
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e3551
            | exact resolve b4e3551 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3551
          have b4e4226 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e3560
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e3560
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e3560 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3560
          have b4e4248 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b4e4226
          have b4e4264 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e4248
               have r₂ := b4e3511
               grind)
            | exact resolve b4e4248 b4e3511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3511 b4e4248
          have b4e4265 : y = (M.op x y) := by
            first
            | (have r₁ := b4e4264
               have r₂ := b4e21
               grind)
            | exact resolve b4e4264 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4264
          have b4e4699 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e4265
               grind)
            | exact superpose b4e4265 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e4265
               grind)
            | exact resolve b4e17 b4e4265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e4720 : x = y ∨ y = (k y x) := by grind
          clear b4e4699
          have b4e4733 : y = (k y x) := by
            first
            | (have r₁ := b4e4720
               have r₂ := b4e21
               grind)
            | exact resolve b4e4720 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4720
          have b4e5489 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e264 x y
               have i₂ := b4e4733
               grind)
            | exact superpose b4e4733 b4e264
            | (have j0 := b4e264 x y
               grind)
            | exact resolve b4e264 b4e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264 b4e4733
          have b4e5492 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b4e5489
          have b4e5494 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e5492
               have r₂ := b4e23
               grind)
            | exact resolve b4e5492 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5492
          have b4e6330 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e5494
               grind)
            | exact superpose b4e5494 b4e20
            | exact resolve b4e20 b4e5494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5494
          have b4e6384 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e6330
               have i₂ := b4e4265
               grind)
            | exact superpose b4e4265 b4e6330
            | exact resolve b4e6330 b4e4265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4265 b4e6330
          have b4e6385 : False := by grind
          exact b4e6385
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e38 : x ≠ x ∨ x = y ∨ x = (k x y) := by
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
          have b5e41 : x = y ∨ x = (k x y) := by grind
          clear b5e38
          have b5e42 : x = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e45 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e226 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e45 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e2293 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e226 y x
               have i₂ := b5e42
               grind)
            | exact superpose b5e42 b5e226
            | (have j0 := b5e226 y x
               grind)
            | exact resolve b5e226 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e226
          have b5e2300 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e2293
          have b5e2303 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e2300
               have r₂ := b5e24
               grind)
            | exact resolve b5e2300 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2300
          have b5e2307 : False := by grind
          exact b5e2307
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
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e42 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e42
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e23
               grind)
            | exact resolve b7e44 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e46 : (σ x) = (σ (k x y)) := by
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
          have b7e49 : (k x y) = (τ (σ x)) := by
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
          have b7e50 : x = (k x y) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e49
            | exact resolve b7e49 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
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
          have b7e61 : x = (M.op y x) ∨ x = y := by grind
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
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e147 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e156 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e147
               have r₂ := b8e23
               grind)
            | exact resolve b8e147 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e1242 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e156
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e156
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e156
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e156
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e156 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1243 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e1242
          have b8e1244 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e1243
               have r₂ := b8e21
               grind)
            | exact resolve b8e1243 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1243
          have b8e1246 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1244
               grind)
            | exact superpose b8e1244 b8e20
            | exact resolve b8e20 b8e1244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1250 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e1244
               grind)
            | exact superpose b8e1244 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e1244
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1244
               grind)
            | exact resolve b8e17 b8e1244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1244
          have b8e1264 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e1250
          have b8e1273 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e1264
               have r₂ := b8e23
               grind)
            | exact resolve b8e1264 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1264
          have b8e1276 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1273
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1273
            | exact resolve b8e1273 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1273
          have b8e1449 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e1276
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1276
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e1276 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1276
          have b8e1470 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e1449
          have b8e1486 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e1470
               have r₂ := b8e1246
               grind)
            | exact resolve b8e1470 b8e1246
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1246 b8e1470
          have b8e1487 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1486
               have r₂ := b8e21
               grind)
            | exact resolve b8e1486 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1486
          have b8e1528 : y ≠ y ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e1487
               grind)
            | exact superpose b8e1487 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1487
               grind)
            | exact resolve b8e17 b8e1487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1544 : x = y ∨ y = (k y x) := by grind
          clear b8e1528
          have b8e1551 : y = (k y x) := by
            first
            | (have r₁ := b8e1544
               have r₂ := b8e21
               grind)
            | exact resolve b8e1544 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1544
          have b8e1600 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e156
               have i₂ := b8e1551
               grind)
            | exact superpose b8e1551 b8e156
            | exact resolve b8e156 b8e1551
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156 b8e1551
          have b8e1604 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1600
               have i₂ := b8e1487
               grind)
            | exact superpose b8e1487 b8e1600
            | exact resolve b8e1600 b8e1487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1600
          have b8e1605 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e1604
          have b8e1732 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1605
               grind)
            | exact superpose b8e1605 b8e20
            | exact resolve b8e20 b8e1605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1605
          have b8e1767 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b8e1732
               have i₂ := b8e1487
               grind)
            | exact superpose b8e1487 b8e1732
            | exact resolve b8e1732 b8e1487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1487 b8e1732
          have b8e1768 : False := by grind
          exact b8e1768

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation731 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
            intro X0 X1 X2
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
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
               have i₂ := b4e13 X0 (M.op X2 X2) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
               have i₂ := b4e13 X0 (M.op X2 X2) X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e93 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 X2 (σ X0) X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e33
            | exact resolve b4e33 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e105 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3))) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X3 (M.op X1 X1) X2
               have i₂ := b4e33 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X0 X1
               grind)
            | (have i₁ := b4e13 X3 (M.op X1 X1) X2
               have i₂ := b4e33 (M.op (M.op X1 X1) (M.op (M.op X2 X2) X3)) X1 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e131 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b4e32 X1 X4 x x
               have i₂ := b4e32 X1 X0 x x
               grind)
            | (have i₁ := b4e32 X0 X1 x x
               have i₂ := b4e32 X0 (M.op x x) x x
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e137 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b4e32 (M.op X5 X2) X5 X3 X4
               have i₂ := b4e32 X2 X5 X0 X1
               grind)
            | (have i₁ := b4e32 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
               have i₂ := b4e32 X0 X1 X2 X3
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e149 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b4e13 (M.op (M.op X4 X4) X1) X2 x
               have i₂ := b4e32 X1 X0 x X4
               grind)
            | (have i₁ := b4e13 (M.op (M.op X2 X2) X0) X1 X2
               have i₂ := b4e32 X0 (M.op X2 X2) X2 x
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e150 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 (M.op X2 X2) x
               have i₂ := b4e32 X1 X0 X2 x
               grind)
            | (have i₁ := b4e13 X0 (M.op X2 X2) X2
               have i₂ := b4e32 X0 (M.op X2 X2) X2 x
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e213 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          clear b4e51
          have b4e219 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e213
               have r₂ := b4e23
               grind)
            | exact resolve b4e213 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e213
          have b4e257 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 (M.op X2 (M.op (M.op X3 X3) X0)))) = (M.op X2 X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e131 X1 (M.op X2 (M.op (M.op X3 X3) X0)) X2
               have i₂ := b4e13 X0 X2 X3
               grind)
            | exact superpose b4e13 b4e131
            | exact resolve b4e131 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e131 X0 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e131
            | exact resolve b4e131 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e268 : ∀ X0 : G, (M.op X0 (M.op X0 x)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b4e131 X0 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e131
            | exact resolve b4e131 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131
          have b4e298 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e264 X0
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e264
            | exact resolve b4e264 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264
          have b4e310 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b4e13 x (M.op X0 X0) X0
               have i₂ := b4e268 (M.op X0 X0)
               grind)
            | exact superpose b4e268 b4e13
            | exact resolve b4e13 b4e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e268
          have b4e339 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e150 (σ X0) (σ X0) X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e150
            | exact resolve b4e150 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e386 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (M.op y y)
               have i₂ := b4e310 y
               grind)
            | exact superpose b4e310 b4e13
            | exact resolve b4e13 b4e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e390 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 X1 (M.op y y) X0
               have i₂ := b4e310 y
               grind)
            | exact superpose b4e310 b4e33
            | exact resolve b4e33 b4e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e391 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e150 X0 X1 (M.op y y)
               have i₂ := b4e310 y
               grind)
            | exact superpose b4e310 b4e150
            | exact resolve b4e150 b4e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e501 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e93 (M.op y y) X0 X1
               have i₂ := b4e310 y
               grind)
            | exact superpose b4e310 b4e93
            | exact resolve b4e93 b4e310
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e310
          have b4e548 : ∀ X0 X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 X0) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (M.op X1 X1)
               have i₂ := b4e93 X1 X0 (σ (M.op X1 X1))
               grind)
            | exact superpose b4e93 b4e30
            | exact resolve b4e30 b4e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93
          have b4e594 : ∀ X1 : G, (σ (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op x (σ (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b4e548 x X1
               have i₂ := b4e390 x (σ (M.op X1 X1))
               grind)
            | exact superpose b4e390 b4e548
            | exact resolve b4e548 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e548
          have b4e621 : ∀ X1 : G, (M.op x X1) = (M.op (σ x) X1) := by
            intro X1
            first
            | (have i₁ := b4e501 x X1
               have i₂ := b4e390 x X1
               grind)
            | exact superpose b4e390 b4e501
            | exact resolve b4e501 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e501
          have b4e646 : ∀ X1 : G, (σ (M.op x (M.op X1 X1))) = (M.op x (σ (M.op X1 X1))) := by
            intro X1
            first
            | (have i₁ := b4e594 X1
               have i₂ := b4e390 X1 (M.op X1 X1)
               grind)
            | exact superpose b4e390 b4e594
            | exact resolve b4e594 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e594
          have b4e807 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 X0)) = (M.op X2 (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e150 X2 (M.op X2 (M.op x X0)) X1
               have i₂ := b4e386 X2 X0
               grind)
            | exact superpose b4e386 b4e150
            | exact resolve b4e150 b4e386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e150 b4e386
          have b4e830 : ∀ X0 X2 : G, (M.op x (M.op X2 X0)) = (M.op X2 (M.op x X0)) := by
            intro X0 X2
            first
            | (have i₁ := b4e807 X0 x X2
               have i₂ := b4e390 x (M.op X2 X0)
               grind)
            | exact superpose b4e390 b4e807
            | exact resolve b4e807 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e807
          have b4e1042 : (σ x) = (M.op x (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b4e391 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e391
            | exact resolve b4e391 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e391
          have b4e1085 : (σ x) = (M.op x (σ (M.op y y))) := by
            first
            | (have i₁ := b4e1042
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e1042
            | exact resolve b4e1042 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1042
          have b4e1096 : (σ x) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b4e1085
               have i₂ := b4e646 y
               grind)
            | exact superpose b4e646 b4e1085
            | exact resolve b4e1085 b4e646
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1085
          have b4e1098 : (σ x) = (σ (M.op y (M.op x y))) := by
            first
            | (have i₁ := b4e1096
               have i₂ := b4e830 y y
               grind)
            | exact superpose b4e830 b4e1096
            | exact resolve b4e1096 b4e830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1096
          have b4e5033 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e219
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e219
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e219
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e219
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e219 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e219
          have b4e5034 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e5033
          have b4e5035 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e5034
               have r₂ := b4e21
               grind)
            | exact resolve b4e5034 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5034
          have b4e5036 : (σ x) = (M.op x (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e5035
               have i₂ := b4e621 (σ y)
               grind)
            | exact superpose b4e621 b4e5035
            | exact resolve b4e5035 b4e621
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e621 b4e5035
          have b4e18821 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 : G, (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) = (M.op X7 (M.op X7 (M.op X2 (M.op (M.op X0 X0) (M.op (M.op X1 X1) (M.op X2 X3)))))) := by
            intro X0 X1 X2 X3 X4 X5 X6 X7
            first
            | (have i₁ := b4e149 X2 (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3)) X7 X4
               have i₂ := b4e137 X5 X6 X3 X0 X1 X2
               grind)
            | (have i₁ := b4e149 (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2)) X2 X4
               have i₂ := b4e137 X0 X1 X2 X3 X4 X5
               grind)
            | exact superpose b4e137 b4e149
            | exact resolve b4e149 b4e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137 b4e149
          have b4e18938 : ∀ X1 X2 X3 X4 X5 X6 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) = (M.op (M.op X4 X4) (M.op (M.op X5 X5) (M.op (M.op X6 X6) X3))) := by
            intro X1 X2 X3 X4 X5 X6
            first
            | (have i₁ := b4e18821 x X1 X2 X3 X4 X5 X6 x
               have i₂ := b4e257 (M.op (M.op X1 X1) (M.op X2 X3)) x X2 x
               grind)
            | exact superpose b4e257 b4e18821
            | exact resolve b4e18821 b4e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e257 b4e18821
          have b4e19548 : ∀ X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X2 X3))) = X3 := by
            intro X1 X2 X3
            first
            | (have i₁ := b4e18938 X1 X2 X3 x x x
               have i₂ := b4e105 x x x X3
               grind)
            | exact superpose b4e105 b4e18938
            | exact resolve b4e18938 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105 b4e18938
          have b4e20058 : ∀ X2 X3 : G, (M.op X2 (M.op x (M.op X2 X3))) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b4e19548 x X2 X3
               have i₂ := b4e390 x (M.op X2 X3)
               grind)
            | exact superpose b4e390 b4e19548
            | exact resolve b4e19548 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e19548
          have b4e28928 : (σ y) = (M.op x (M.op x (σ x))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20058 x (σ y)
               have i₂ := b4e5036
               grind)
            | exact superpose b4e5036 b4e20058
            | exact resolve b4e20058 b4e5036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5036 b4e20058
          have b4e28929 : (σ y) = (σ (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e28928
               have i₂ := b4e298 x
               grind)
            | exact superpose b4e298 b4e28928
            | exact resolve b4e28928 b4e298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e298 b4e28928
          have b4e59834 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e339 y X0
               have i₂ := b4e28929
               grind)
            | exact superpose b4e28929 b4e339
            | exact resolve b4e339 b4e28929
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e339 b4e28929
          have b4e59904 : (σ y) = (M.op x (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e59834 x
               have i₂ := b4e390 x (M.op (σ y) (σ y))
               grind)
            | exact superpose b4e390 b4e59834
            | exact resolve b4e59834 b4e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e390 b4e59834
          have b4e59918 : (σ y) = (M.op x (σ (M.op y y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e59904
               have i₂ := b4e30 y
               grind)
            | exact superpose b4e30 b4e59904
            | exact resolve b4e59904 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e59904
          have b4e59923 : (σ y) = (σ (M.op x (M.op y y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e59918
               have i₂ := b4e646 y
               grind)
            | exact superpose b4e646 b4e59918
            | exact resolve b4e59918 b4e646
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e646 b4e59918
          have b4e59924 : (σ y) = (σ (M.op y (M.op x y))) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e59923
               have i₂ := b4e830 y y
               grind)
            | exact superpose b4e830 b4e59923
            | exact resolve b4e59923 b4e830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e830 b4e59923
          have b4e59925 : (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e59924
               have i₂ := b4e1098
               grind)
            | exact superpose b4e1098 b4e59924
            | exact resolve b4e59924 b4e1098
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59924
          have b4e59926 : x = (M.op x y) := by
            first
            | (have r₁ := b4e59925
               have r₂ := b4e23
               grind)
            | exact resolve b4e59925 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59925
          have b4e60008 : (σ x) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e1098
               have i₂ := b4e59926
               grind)
            | exact superpose b4e59926 b4e1098
            | exact resolve b4e1098 b4e59926
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1098 b4e59926
          have b4e60049 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e60008
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e60008
            | exact resolve b4e60008 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60008
          have b4e60060 : False := by grind
          exact b4e60060
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
          have b5e41 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e43 : x = y ∨ y = (k x y) := by grind
          clear b5e41
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
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
          have b5e212 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e17031 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e212 y x
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e212
            | (have j0 := b5e212 y x
               grind)
            | exact resolve b5e212 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e212
          have b5e17034 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
          clear b5e17031
          have b5e17038 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e17034
               have r₂ := b5e24
               grind)
            | exact resolve b5e17034 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17034
          have b5e17043 : False := by grind
          exact b5e17043
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
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e43 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e41
          have b7e44 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e23
               grind)
            | exact resolve b7e43 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e45 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e44
            | exact resolve b7e44 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e48 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e14
            | exact resolve b7e14 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e49 : y = (k x y) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e48
            | exact resolve b7e48 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e59 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e49
               grind)
            | exact superpose b7e49 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e60 : y = (M.op y x) ∨ x = y := by grind
          clear b7e59
          have b7e62 : x = y := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e22
               grind)
            | exact resolve b7e60 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e64 : False := by grind
          exact b7e64
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
          have b8e186 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e192 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e186
               have r₂ := b8e23
               grind)
            | exact resolve b8e186 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e186
          have b8e4525 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e192
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e192
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e192
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e192
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e192 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4526 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e4525
          have b8e4527 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e4526
               have r₂ := b8e21
               grind)
            | exact resolve b8e4526 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4526
          have b8e4529 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e4527
               grind)
            | exact superpose b8e4527 b8e20
            | exact resolve b8e20 b8e4527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4530 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e4527
               grind)
            | exact superpose b8e4527 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e4527
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e4527
               grind)
            | exact resolve b8e17 b8e4527
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4527
          have b8e4539 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e4530
          have b8e4548 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e4539
               have r₂ := b8e23
               grind)
            | exact resolve b8e4539 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4539
          have b8e4553 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e4548
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e4548
            | exact resolve b8e4548 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4548
          have b8e5334 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e4553
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e4553
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e4553 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4553
          have b8e5353 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e5334
          have b8e5369 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e5353
               have r₂ := b8e4529
               grind)
            | exact resolve b8e5353 b8e4529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4529 b8e5353
          have b8e5370 : x = (M.op x y) := by
            first
            | (have r₁ := b8e5369
               have r₂ := b8e21
               grind)
            | exact resolve b8e5369 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5369
          have b8e5939 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e5370
               grind)
            | exact superpose b8e5370 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e5370
               grind)
            | exact resolve b8e17 b8e5370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e5948 : x = y ∨ x = (k y x) := by grind
          clear b8e5939
          have b8e5949 : x = (k y x) := by
            first
            | (have r₁ := b8e5948
               have r₂ := b8e21
               grind)
            | exact resolve b8e5948 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5948
          have b8e6533 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e192
               have i₂ := b8e5949
               grind)
            | exact superpose b8e5949 b8e192
            | exact resolve b8e192 b8e5949
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192 b8e5949
          have b8e6537 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e6533
               have i₂ := b8e5370
               grind)
            | exact superpose b8e5370 b8e6533
            | exact resolve b8e6533 b8e5370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6533
          have b8e6538 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e6537
          have b8e7229 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6538
               grind)
            | exact superpose b8e6538 b8e20
            | exact resolve b8e20 b8e6538
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6538
          have b8e7249 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e7229
               have i₂ := b8e5370
               grind)
            | exact superpose b8e5370 b8e7229
            | exact resolve b8e7229 b8e5370
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5370 b8e7229
          have b8e7250 : False := by grind
          exact b8e7250
