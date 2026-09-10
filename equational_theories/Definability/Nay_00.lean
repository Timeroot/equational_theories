import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2126`: `x = ((y ◇ y) ◇ x) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pxy_Equation2126 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2126 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2126.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e46 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x X0
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e19
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 (σ y) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) X0
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e20
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e158 : (M.op x y) = (k y x) := by
        first
        | (have j0 := b0e46 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e527 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
        first
        | (have j0 := b0e48 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e529 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e527
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e527
        | exact resolve b0e527 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e527
      have b0e539 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e529
           have i₂ := b0e158
           grind)
        | exact superpose b0e158 b0e529
        | exact resolve b0e529 b0e158
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e158 b0e529
      have b0e543 : False := by grind
      exact b0e543
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : False := by grind
        exact b1e25
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e55 (σ X0)
             grind)
          | exact superpose b2e55 b2e18
          | exact resolve b2e18 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e57 X0
             have i₂ := b2e55 X0
             grind)
          | exact superpose b2e55 b2e57
          | exact resolve b2e57 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e57
        have b2e136 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e64 y
             grind)
          | exact superpose b2e64 b2e21
          | exact resolve b2e21 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e144 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e136
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e136
          | exact resolve b2e136 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e136
        have b2e145 : False := by grind
        exact b2e145
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e55 (σ X0)
             grind)
          | exact superpose b6e55 b6e18
          | exact resolve b6e18 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e57 X0
             have i₂ := b6e55 X0
             grind)
          | exact superpose b6e55 b6e57
          | exact resolve b6e57 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e57
        have b6e139 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e64 y
             grind)
          | exact superpose b6e64 b6e22
          | exact resolve b6e22 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e149 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e139
             have i₂ := b6e64 x
             grind)
          | exact superpose b6e64 b6e139
          | exact resolve b6e139 b6e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e64 b6e139
        have b6e172 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e149
             grind)
          | exact superpose b6e149 b6e13
          | exact resolve b6e13 b6e149
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e173 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e172
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e172
          | exact resolve b6e172 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e172
        have b6e179 : False := by grind
        exact b6e179
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e27 : False := by grind
          exact b7e27
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e45 (σ X0)
               grind)
            | exact superpose b8e45 b8e19
            | exact resolve b8e19 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e47 X0
               have i₂ := b8e45 X0
               grind)
            | exact superpose b8e45 b8e47
            | exact resolve b8e47 b8e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45 b8e47
          have b8e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (σ X1) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e73 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 X0 y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e84 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e63 X0 X1
               have i₂ := b8e52 X1
               grind)
            | exact superpose b8e52 b8e63
            | (have j0 := b8e63 X0 X1
               grind)
            | exact resolve b8e63 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84 X0 X1
               have i₂ := b8e52 X0
               grind)
            | exact superpose b8e52 b8e84
            | (have j0 := b8e84 X0 X1
               grind)
            | exact resolve b8e84 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84
          have b8e154 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e52 y
               grind)
            | exact superpose b8e52 b8e23
            | exact resolve b8e23 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e164 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e154
               have i₂ := b8e52 x
               grind)
            | exact superpose b8e52 b8e154
            | exact resolve b8e154 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52 b8e154
          have b8e171 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e73 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e172 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e171
               have r₂ := b8e22
               grind)
            | exact resolve b8e171 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e171
          have b8e841 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e86 x y
               grind)
            | exact superpose b8e86 b8e20
            | (have j1 := b8e86 x y
               grind)
            | exact resolve b8e20 b8e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e86
          have b8e888 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e841
               have r₂ := b8e164
               grind)
            | exact resolve b8e841 b8e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164 b8e841
          have b8e911 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e888
               have r₂ := b8e24
               grind)
            | exact resolve b8e888 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e888
          have b8e930 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e911
               have i₂ := b8e172
               grind)
            | exact superpose b8e172 b8e911
            | exact resolve b8e911 b8e172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e172 b8e911
          have b8e931 : False := by grind
          exact b8e931

/-- `Equation2552`: `x = (y ◇ ((y ◇ z) ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(X,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxx_pxx_pxy_Equation2552 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2552 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2552.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X2) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X0 X3)) X2) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 X1 (M.op (M.op X1 X2) X0)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e165 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X2 := by
        intro X0 X2
        first
        | (have i₁ := b0e34 X0 x (M.op X0 X2) X2
           have i₂ := b0e11 X0 x (M.op X0 X2)
           grind)
        | exact superpose b0e11 b0e34
        | exact resolve b0e34 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e167 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 (M.op X1 X0) X1 X2 (M.op (M.op X1 X2) (M.op X1 X0))
           have i₂ := b0e35 (M.op (M.op X1 X2) (M.op X1 X0)) X1 X0
           grind)
        | exact superpose b0e35 b0e34
        | exact resolve b0e34 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e202 : x = (M.op x y) := by
        first
        | (have i₁ := b0e165 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e165
        | exact resolve b0e165 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e212 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op (M.op X1 X0) X2) X1 X0
           have i₂ := b0e165 (M.op X1 X0) X2
           grind)
        | exact superpose b0e165 b0e11
        | exact resolve b0e11 b0e165
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e165
      have b0e241 : ∀ X0 : G, (M.op (M.op x (M.op x X0)) y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x y
           have i₂ := b0e202
           grind)
        | exact superpose b0e202 b0e11
        | exact resolve b0e11 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e245 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e35 X0 x y
           have i₂ := b0e202
           grind)
        | exact superpose b0e202 b0e35
        | exact resolve b0e35 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e249 : ∀ X0 : G, (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e245 X0
           have i₂ := b0e167 X0 x X0
           grind)
        | exact superpose b0e167 b0e245
        | exact resolve b0e245 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e245
      have b0e252 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e241 X0
           have i₂ := b0e212 y x (M.op x X0)
           grind)
        | (have i₁ := b0e241 X0
           have i₂ := b0e212 (M.op x X0) x y
           grind)
        | exact superpose b0e212 b0e241
        | exact resolve b0e241 b0e212
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e212 b0e241
      have b0e255 : ∀ X0 : G, (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e252 X0
           have i₂ := b0e167 X0 x y
           grind)
        | exact superpose b0e167 b0e252
        | exact resolve b0e252 b0e167
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e167 b0e252
      have b0e283 : y = (σ y) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e249 (σ x)
           grind)
        | exact superpose b0e249 b0e20
        | exact resolve b0e20 b0e249
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e249
      have b0e385 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e283
           grind)
        | exact superpose b0e283 b0e18
        | exact resolve b0e18 b0e283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283
      have b0e393 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e385
           have i₂ := b0e255 (σ x)
           grind)
        | exact superpose b0e255 b0e385
        | exact resolve b0e385 b0e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e255 b0e385
      have b0e397 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e393
           have i₂ := b0e202
           grind)
        | exact superpose b0e202 b0e393
        | exact resolve b0e393 b0e202
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e202 b0e393
      have b0e398 : False := by grind
      exact b0e398
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : y = (k x y) := by grind
        have b1e35 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e38 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e35
        have b1e39 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e38
             have r₂ := b1e21
             grind)
          | exact resolve b1e38 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e40 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e39
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e39
          | exact resolve b1e39 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e40
          | exact resolve b1e40 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e40
        have b1e42 : False := by grind
        exact b1e42
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : y = (k x y) := by grind
        have b2e48 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e209 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e48 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e210 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e209
             have r₂ := b2e22
             grind)
          | exact resolve b2e209 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e209
        have b2e211 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e210
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e210
          | exact resolve b2e210 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e210
        have b2e212 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e211
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e211
          | exact resolve b2e211 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e211
        have b2e213 : False := by grind
        exact b2e213
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e26 : (σ y) = (σ (k x y)) := by
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
        have b3e31 : (k x y) = (τ (σ y)) := by
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
        have b3e32 : y = (k x y) := by
          first
          | (have i₁ := b3e31
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e31
          | exact resolve b3e31 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e39 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e42 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e39
        have b3e43 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e20
             grind)
          | exact resolve b3e42 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e44 : y = (M.op x x) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e32
             grind)
          | exact superpose b3e32 b3e43
          | exact resolve b3e43 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e43
        have b3e45 : False := by grind
        exact b3e45
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b5e34 : ∀ X0 : G, (M.op (M.op x (M.op y X0)) y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X0 X3)) X2) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X2 X1 (M.op (M.op X1 X2) X0)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 y x (M.op y X0)
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : y ≠ y ∨ y = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
          have b5e42 : y = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
          clear b5e39
          have b5e43 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e42
               have r₂ := b5e21
               grind)
            | exact resolve b5e42 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e55 : y = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b5e37 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e37
            | exact resolve b5e37 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e82 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op X1 X2) X3) (M.op X0 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X3 (M.op X1 X2) (M.op (M.op X1 X0) X2)
               have i₂ := b5e36 X2 X1 X0
               grind)
            | exact superpose b5e36 b5e36
            | exact resolve b5e36 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e90 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X3)) (M.op (M.op X1 X0) X2)) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 (M.op X1 X2) (M.op (M.op X1 X0) X2)
               have i₂ := b5e36 X2 X1 X0
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e106 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X2) (M.op X0 X3)) (M.op X3 X4)) (M.op (M.op X1 X0) X2)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e35 X3 (M.op X1 X2) (M.op (M.op X1 X0) X2) X4
               have i₂ := b5e36 X2 X1 X0
               grind)
            | exact superpose b5e36 b5e35
            | exact resolve b5e35 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e108 : ∀ X0 X1 : G, (M.op (M.op (M.op y (M.op y X0)) (M.op X0 X1)) (M.op y y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 y (M.op y y) X1
               have i₂ := b5e55
               grind)
            | exact superpose b5e55 b5e35
            | exact resolve b5e35 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e125 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b5e35 X0 x (M.op X0 X2) X2
               have i₂ := b5e13 X0 x (M.op X0 X2)
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e127 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 (M.op X1 X0) X1 X2 (M.op (M.op X1 X2) (M.op X1 X0))
               have i₂ := b5e36 (M.op (M.op X1 X2) (M.op X1 X0)) X1 X0
               grind)
            | exact superpose b5e36 b5e35
            | exact resolve b5e35 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e145 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op y y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e108 X0 X1
               have i₂ := b5e125 y X0
               grind)
            | (have i₁ := b5e108 X0 X1
               have i₂ := b5e125 X0 (M.op y (M.op y X0))
               grind)
            | exact superpose b5e125 b5e108
            | exact resolve b5e108 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e108
          have b5e149 : ∀ X1 : G, (M.op X1 (M.op y y)) = X1 := by
            intro X1
            first
            | (have i₁ := b5e145 x X1
               have i₂ := b5e125 x X1
               grind)
            | (have i₁ := b5e145 x X1
               have i₂ := b5e125 x (M.op x (M.op x X1))
               grind)
            | exact superpose b5e125 b5e145
            | exact resolve b5e145 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145
          have b5e169 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op (M.op X1 X0) X2) X1 X0
               have i₂ := b5e125 (M.op X1 X0) X2
               grind)
            | exact superpose b5e125 b5e13
            | exact resolve b5e13 b5e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e204 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e125 X0 (M.op y y)
               have i₂ := b5e149 X0
               grind)
            | exact superpose b5e149 b5e125
            | exact resolve b5e125 b5e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e233 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e54 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54
          have b5e234 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e233
               have r₂ := b5e24
               grind)
            | exact resolve b5e233 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e233
          have b5e235 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e234
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e234
            | exact resolve b5e234 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e234
          have b5e236 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e235
               have i₂ := b5e43
               grind)
            | exact superpose b5e43 b5e235
            | exact resolve b5e235 b5e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43 b5e235
          have b5e238 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e204 X0
               have i₂ := b5e204 X1
               grind)
            | (have i₁ := b5e204 X0
               have i₂ := b5e204 y
               grind)
            | exact superpose b5e204 b5e204
            | exact resolve b5e204 b5e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e240 : ∀ X0 : G, (M.op y y) = (k X0 (M.op y y)) := by
            intro X0
            grind
          have b5e253 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e149 X1
               have i₂ := b5e204 X0
               grind)
            | (have i₁ := b5e149 X1
               have i₂ := b5e204 y
               grind)
            | exact superpose b5e204 b5e149
            | exact resolve b5e149 b5e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e149
          have b5e397 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e47 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e399 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e397 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e397
          have b5e410 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b5e399 X0
               have i₂ := b5e204 (σ X0)
               grind)
            | exact superpose b5e204 b5e399
            | (have j0 := b5e399 X0
               grind)
            | exact resolve b5e399 b5e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e399
          have b5e816 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e125 (σ x) (σ y)
               have i₂ := b5e236
               grind)
            | exact superpose b5e236 b5e125
            | exact resolve b5e125 b5e236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125 b5e236
          have b5e855 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X0 X1) (M.op (M.op X3 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e127 X2 (M.op X3 X1) (M.op X3 X0)
               have i₂ := b5e127 X0 X3 X1
               grind)
            | exact superpose b5e127 b5e127
            | exact resolve b5e127 b5e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2002 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op y y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e410 (M.op y y)
               have i₂ := b5e240 (M.op y y)
               grind)
            | exact superpose b5e240 b5e410
            | (have j0 := b5e410 (M.op y y)
               grind)
            | exact resolve b5e410 b5e240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e240 b5e410
          have b5e2013 : (M.op y y) = (σ (M.op y y)) := by grind
          clear b5e2002
          have b5e2100 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e2013
               have i₂ := b5e238 y x
               grind)
            | (have i₁ := b5e2013
               have i₂ := b5e238 X0 y
               grind)
            | exact superpose b5e238 b5e2013
            | exact resolve b5e2013 b5e238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e238
          have b5e3391 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X4) = (M.op (M.op (M.op X1 X4) (M.op (M.op X2 X0) X3)) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e82 (M.op X2 X3) X1 X4 (M.op (M.op X2 X0) X3)
               have i₂ := b5e36 X3 X2 X0
               grind)
            | exact superpose b5e36 b5e82
            | exact resolve b5e82 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3550 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X4) = (M.op (M.op (M.op X1 X4) X0) (M.op (M.op X2 X0) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e3391 X0 X1 X2 X3 X4
               have i₂ := b5e169 X0 (M.op X1 X4) (M.op (M.op X2 X0) X3)
               grind)
            | (have i₁ := b5e3391 X0 X1 X2 X3 X4
               have i₂ := b5e169 (M.op (M.op X2 X0) X3) (M.op X1 X4) X0
               grind)
            | exact superpose b5e169 b5e3391
            | exact resolve b5e3391 b5e169
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e169 b5e3391
          have b5e3641 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X2 X3)) X4) = (M.op X3 (M.op X2 (M.op X1 X4))) := by
            intro X1 X2 X3 X4
            first
            | (have i₁ := b5e3550 x X1 X2 X3 X4
               have i₂ := b5e855 (M.op X1 X4) x X3 X2
               grind)
            | exact superpose b5e855 b5e3550
            | exact resolve b5e3550 b5e855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e855 b5e3550
          have b5e4023 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X4 X0)) = (M.op X0 (M.op X3 (M.op (M.op X1 X4) X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e82 X3 (M.op X1 X2) (M.op X4 X0) (M.op (M.op X1 X4) X2)
               have i₂ := b5e90 X4 X1 X2 X0
               grind)
            | exact superpose b5e90 b5e82
            | exact resolve b5e82 b5e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82 b5e90
          have b5e6175 : (σ y) = (M.op (σ x) (M.op x x)) := by
            first
            | (have i₁ := b5e816
               have i₂ := b5e2100 x
               grind)
            | exact superpose b5e2100 b5e816
            | exact resolve b5e816 b5e2100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e816 b5e2100
          have b5e6230 : (σ x) = (σ y) := by
            first
            | (have i₁ := b5e6175
               have i₂ := b5e253 x (σ x)
               grind)
            | exact superpose b5e253 b5e6175
            | exact resolve b5e6175 b5e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e253 b5e6175
          have b5e6530 : y = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 y
               have i₂ := b5e6230
               grind)
            | exact superpose b5e6230 b5e14
            | exact resolve b5e14 b5e6230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6230
          have b5e6561 : x = y := by
            first
            | (have i₁ := b5e6530
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e6530
            | exact resolve b5e6530 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6530
          have b5e6688 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) X5) = (M.op (M.op (M.op (M.op X1 X2) (M.op X3 (M.op X4 X5))) X0) (M.op (M.op X1 X3) X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e106 X3 X1 X2 (M.op X4 X5) (M.op (M.op X4 X0) X5)
               have i₂ := b5e36 X5 X4 X0
               grind)
            | exact superpose b5e36 b5e106
            | exact resolve b5e106 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e6697 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op (M.op (M.op X1 X2) (M.op X3 (M.op x (M.op y X0)))) X0) (M.op (M.op X1 X3) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e106 X3 X1 X2 (M.op x (M.op y X0)) y
               have i₂ := b5e34 X0
               grind)
            | exact superpose b5e34 b5e106
            | exact resolve b5e106 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e106
          have b5e6975 : ∀ X0 X1 X2 X3 : G, y = (M.op X2 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X3 (M.op x (M.op y X0)))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e6697 X0 X1 X2 X3
               have i₂ := b5e4023 X2 (M.op X1 X2) (M.op X3 (M.op x (M.op y X0))) X0 (M.op X1 X3)
               grind)
            | exact superpose b5e4023 b5e6697
            | exact resolve b5e6697 b5e4023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6697
          have b5e6984 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) X5) = (M.op X2 (M.op X0 (M.op (M.op (M.op X1 X2) (M.op X1 X3)) (M.op X3 (M.op X4 X5))))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e6688 X0 X1 X2 X3 X4 X5
               have i₂ := b5e4023 X2 (M.op X1 X2) (M.op X3 (M.op X4 X5)) X0 (M.op X1 X3)
               grind)
            | exact superpose b5e4023 b5e6688
            | exact resolve b5e6688 b5e4023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4023 b5e6688
          have b5e7228 : ∀ X0 X1 X2 X3 : G, y = (M.op X2 (M.op X0 (M.op X3 (M.op X1 (M.op (M.op X1 X2) (M.op X3 (M.op x (M.op y X0)))))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e6975 X0 X1 X2 X3
               have i₂ := b5e3641 (M.op X1 X2) X1 X3 (M.op X3 (M.op x (M.op y X0)))
               grind)
            | (have i₁ := b5e6975 X0 X1 X2 X2
               have i₂ := b5e3641 x X2 (M.op (M.op X1 X2) (M.op X1 X2)) (M.op y X0)
               grind)
            | exact superpose b5e3641 b5e6975
            | exact resolve b5e6975 b5e3641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6975
          have b5e7237 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X0) X5) = (M.op X2 (M.op X0 (M.op X3 (M.op X1 (M.op (M.op X1 X2) (M.op X3 (M.op X4 X5))))))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e6984 X0 X1 X2 X3 X4 X5
               have i₂ := b5e3641 (M.op X1 X2) X1 X3 (M.op X3 (M.op X4 X5))
               grind)
            | (have i₁ := b5e6984 X0 X1 X2 X2 X1 X4
               have i₂ := b5e3641 X1 X2 (M.op (M.op X1 X2) (M.op X1 X2)) X4
               grind)
            | exact superpose b5e3641 b5e6984
            | exact resolve b5e6984 b5e3641
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3641 b5e6984
          have b5e7474 : ∀ X0 X1 X2 X3 : G, x = (M.op X2 (M.op X0 (M.op X3 (M.op X1 (M.op (M.op X1 X2) (M.op X3 (M.op x (M.op x X0)))))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e7228 X0 X1 X2 X3
               have i₂ := b5e6561
               grind)
            | exact superpose b5e6561 b5e7228
            | exact resolve b5e7228 b5e6561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7228
          have b5e7697 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e7474 X0 x x x
               have i₂ := b5e7237 X0 x x x x (M.op x X0)
               grind)
            | exact superpose b5e7237 b5e7474
            | exact resolve b5e7474 b5e7237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7237 b5e7474
          have b5e7889 : ∀ X0 : G, (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b5e7697 X0
               have i₂ := b5e127 X0 x X0
               grind)
            | exact superpose b5e127 b5e7697
            | exact resolve b5e7697 b5e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e127 b5e7697
          have b5e8218 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e6561
               grind)
            | exact superpose b5e6561 b5e24
            | exact resolve b5e24 b5e6561
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6561
          have b5e8260 : (σ x) ≠ (M.op y y) := by
            first
            | (have i₁ := b5e8218
               have i₂ := b5e204 (σ x)
               grind)
            | exact superpose b5e204 b5e8218
            | exact resolve b5e8218 b5e204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e204 b5e8218
          have b5e8266 : x ≠ (σ x) := by
            first
            | (have i₁ := b5e8260
               have i₂ := b5e7889 y
               grind)
            | exact superpose b5e7889 b5e8260
            | exact resolve b5e8260 b5e7889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8260
          have b5e11009 : x = (σ x) := by
            first
            | (have i₁ := b5e2013
               have i₂ := b5e7889 y
               grind)
            | exact superpose b5e7889 b5e2013
            | exact resolve b5e2013 b5e7889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2013 b5e7889
          have b5e11025 : False := by grind
          exact b5e11025
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
        have b6e25 : (σ y) = (σ (k x y)) := by
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
        have b6e26 : (k x y) = (τ (σ y)) := by
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
        have b6e27 : y = (k x y) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e70 : y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e77 : y = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e70
        have b6e80 : y = (M.op x x) := by
          first
          | (have r₁ := b6e77
             have r₂ := b6e21
             grind)
          | exact resolve b6e77 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e83 : False := by grind
        exact b6e83
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 (M.op (M.op X1 X2) X0)) (M.op X0 X3)) X2) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 (M.op X1 (M.op (M.op X1 X2) X0)) X2
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X1 X2) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X2 X1 (M.op (M.op X1 X2) X0)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e23
               grind)
            | exact resolve b7e39 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e41 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e40
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e40
            | exact resolve b7e40 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e63 : (σ (k x y)) = (k (σ x) (σ (k x y))) := by grind
          have b7e66 : (σ (k x y)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e19 x (k x y)
               grind)
            | exact superpose b7e19 b7e63
            | exact resolve b7e63 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63
          have b7e119 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op X1 X2) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e30 (M.op X1 X0) X1 X2 (M.op (M.op X1 X2) (M.op X1 X0))
               have i₂ := b7e31 (M.op (M.op X1 X2) (M.op X1 X0)) X1 X0
               grind)
            | exact superpose b7e31 b7e30
            | exact resolve b7e30 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e120 : ∀ X0 X2 : G, (M.op X0 (M.op X0 X2)) = X2 := by
            intro X0 X2
            first
            | (have i₁ := b7e30 X0 x (M.op X0 X2) X2
               have i₂ := b7e13 X0 x (M.op X0 X2)
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e138 : (σ x) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b7e120 (σ x) (σ x)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e120
            | exact resolve b7e120 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e253 : ∀ X0 : G, (σ (k x y)) = (M.op (M.op (σ x) X0) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b7e31 X0 (σ x) (σ (k x y))
               have i₂ := b7e138
               grind)
            | exact superpose b7e138 b7e31
            | exact resolve b7e31 b7e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e138
          have b7e257 : ∀ X0 : G, (M.op X0 X0) = (σ (k x y)) := by
            intro X0
            first
            | (have i₁ := b7e253 X0
               have i₂ := b7e119 X0 (σ x) X0
               grind)
            | exact superpose b7e119 b7e253
            | exact resolve b7e253 b7e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119 b7e253
          have b7e415 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b7e257 X0
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e257
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e257 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e438 : ∀ X0 : G, (k x y) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e257 X0
               grind)
            | exact superpose b7e257 b7e14
            | exact resolve b7e14 b7e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e457 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have j0 := b7e415 X0
               grind)
            | (have r₁ := b7e415 X0
               have r₂ := b7e21
               grind)
            | exact resolve b7e415 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e415
          have b7e462 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
            intro X0
            first
            | (have j0 := b7e457 X0
               grind)
            | (have r₁ := b7e457 X0
               have r₂ := b7e22
               grind)
            | exact resolve b7e457 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e457
          have b7e633 : (k x (k x y)) = (τ (σ (k x y))) := by
            first
            | (have i₁ := b7e14 (k x (k x y))
               have i₂ := b7e66
               grind)
            | exact superpose b7e66 b7e14
            | exact resolve b7e14 b7e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e648 : (k x y) = (k x (k x y)) := by
            first
            | (have i₁ := b7e633
               have i₂ := b7e14 (k x y)
               grind)
            | exact superpose b7e14 b7e633
            | exact resolve b7e633 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e633
          have b7e1198 : (k x y) = (τ (σ (M.op x y))) := by
            first
            | (have i₁ := b7e438 x
               have i₂ := b7e462 x
               grind)
            | exact superpose b7e462 b7e438
            | exact resolve b7e438 b7e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e438 b7e462
          have b7e1258 : (M.op x y) = (k x y) := by
            first
            | (have i₁ := b7e1198
               have i₂ := b7e14 (M.op x y)
               grind)
            | exact superpose b7e14 b7e1198
            | exact resolve b7e1198 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1198
          have b7e1621 : (k x y) = (M.op x (k x y)) ∨ (M.op x x) = (k x y) ∨ (k x y) = (M.op x (k x y)) := by
            first
            | (have i₁ := b7e18 x (k x y)
               have i₂ := b7e648
               grind)
            | exact superpose b7e648 b7e18
            | (have j0 := b7e18 x (k x y)
               grind)
            | exact resolve b7e18 b7e648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e648
          have b7e1622 : (k x y) = (M.op x (k x y)) ∨ (M.op x x) = (k x y) := by grind
          clear b7e1621
          have b7e1629 : (M.op x y) = (M.op x (M.op x y)) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1622
               have i₂ := b7e1258
               grind)
            | exact superpose b7e1258 b7e1622
            | exact resolve b7e1622 b7e1258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1622
          have b7e1639 : y = (M.op x y) ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1629
               have i₂ := b7e120 x y
               grind)
            | (have i₁ := b7e1629
               have i₂ := b7e120 x (M.op x (M.op x y))
               grind)
            | exact superpose b7e120 b7e1629
            | exact resolve b7e1629 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1629
          have b7e1645 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b7e1639
               have r₂ := b7e22
               grind)
            | exact resolve b7e1639 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1639
          have b7e1727 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e1258
               have i₂ := b7e1645
               grind)
            | exact superpose b7e1645 b7e1258
            | exact resolve b7e1258 b7e1645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1645
          have b7e2690 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b7e120 x y
               have i₂ := b7e1727
               grind)
            | exact superpose b7e1727 b7e120
            | exact resolve b7e120 b7e1727
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e2691 : x = y := by
            first
            | (have i₁ := b7e2690
               have i₂ := b7e120 x x
               grind)
            | (have i₁ := b7e2690
               have i₂ := b7e120 x (M.op x (M.op x x))
               grind)
            | exact superpose b7e120 b7e2690
            | exact resolve b7e2690 b7e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120 b7e2690
          have b7e3074 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e2691
               grind)
            | exact superpose b7e2691 b7e24
            | exact resolve b7e24 b7e2691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3075 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e2691
               grind)
            | exact superpose b7e2691 b7e26
            | exact resolve b7e26 b7e2691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e2691
          have b7e3108 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e3074
               have i₂ := b7e257 (σ x)
               grind)
            | exact superpose b7e257 b7e3074
            | exact resolve b7e3074 b7e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e257 b7e3074
          have b7e3114 : (σ (M.op x y)) = (σ x) := by
            first
            | (have i₁ := b7e3108
               have i₂ := b7e1258
               grind)
            | exact superpose b7e1258 b7e3108
            | exact resolve b7e3108 b7e1258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1258 b7e3108
          have b7e3118 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e3114
               have i₂ := b7e1727
               grind)
            | exact superpose b7e1727 b7e3114
            | exact resolve b7e3114 b7e1727
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1727 b7e3114
          have b7e3120 : False := by grind
          exact b7e3120
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b8e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e164 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e53 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53
          have b8e165 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e164
               have r₂ := b8e24
               grind)
            | exact resolve b8e164 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e164
          have b8e166 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e165
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e165
            | exact resolve b8e165 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e165
          have b8e167 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e166
               grind)
            | exact superpose b8e166 b8e20
            | exact resolve b8e20 b8e166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166
          have b8e347 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e167
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e167
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e167 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167
          have b8e348 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e347
          have b8e352 : y = (M.op x y) := by
            first
            | (have r₁ := b8e348
               have r₂ := b8e21
               grind)
            | exact resolve b8e348 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e348
          have b8e356 : False := by grind
          exact b8e356

/-- `Equation2685`: `x = ((x ◇ y) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation2685 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2685 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2685.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e23 X0 X1
           grind)
        | exact superpose b0e23 b0e12
        | exact resolve b0e12 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e29 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 y y X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 : G, (M.op x (M.op X0 y)) = (M.op (M.op y (M.op X1 X0)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op x (M.op X0 y)) X0 X1
           have i₂ := b0e29 X0
           grind)
        | exact superpose b0e29 b0e11
        | exact resolve b0e11 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (k x y) = (M.op y x) := by grind
      have b0e42 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
      have b0e43 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e42
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e42
        | exact resolve b0e42 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e44 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e43
        | exact resolve b0e43 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e43
      have b0e69 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e85 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 x) y) := by
        intro X0 X1
        first
        | (have i₁ := b0e32 (M.op (M.op X0 X1) (M.op y X1))
           have i₂ := b0e11 X0 X1 y
           grind)
        | exact superpose b0e11 b0e32
        | exact resolve b0e32 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 x) y) := by
        intro X0
        first
        | (have i₁ := b0e32 (M.op (M.op X0 y) x)
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e32
        | exact resolve b0e32 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e95 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 X1) (M.op y X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e85 X0 X1
           have i₂ := b0e88 X0
           grind)
        | exact superpose b0e88 b0e85
        | exact resolve b0e85 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e85
      have b0e127 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 X1 (τ X0)
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e28
        | exact resolve b0e28 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e233 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 x X2
           have i₂ := b0e31 X0 x X2 X1
           grind)
        | exact superpose b0e31 b0e11
        | exact resolve b0e11 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e242 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e29 x
           have i₂ := b0e31 x X0 y x
           grind)
        | exact superpose b0e31 b0e29
        | exact resolve b0e29 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e31
      have b0e254 : y = (M.op (M.op x y) x) := by
        first
        | (have i₁ := b0e242 x
           have i₂ := b0e95 x x
           grind)
        | exact superpose b0e95 b0e242
        | exact resolve b0e242 b0e95
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e95 b0e242
      have b0e271 : ∀ X0 : G, (M.op x y) = (M.op (M.op y (M.op X0 x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (M.op x y) x X0
           have i₂ := b0e254
           grind)
        | exact superpose b0e254 b0e11
        | exact resolve b0e11 b0e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e272 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e271 x
           have i₂ := b0e39 x x
           grind)
        | exact superpose b0e39 b0e271
        | exact resolve b0e271 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e271
      have b0e347 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
           have i₂ := b0e34 (M.op X1 X2) X0 X1 X2
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e439 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op X1 (M.op x y)) (M.op x y))) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e34 X1 X0 x (M.op x y)
           have i₂ := b0e272
           grind)
        | exact superpose b0e272 b0e34
        | exact resolve b0e34 b0e272
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e272
      have b0e440 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e439 X0 X1
           have i₂ := b0e347 (M.op (M.op X0 x) X1) X1 (M.op x y)
           grind)
        | exact superpose b0e347 b0e439
        | exact resolve b0e439 b0e347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e439
      have b0e502 : ∀ X0 : G, (M.op x y) = (M.op (M.op y X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e440 (M.op x y) X0
           have i₂ := b0e254
           grind)
        | exact superpose b0e254 b0e440
        | exact resolve b0e440 b0e254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254
      have b0e703 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        grind
      clear b0e69
      have b0e851 : ∀ X0 : G, (M.op (M.op (M.op X0 y) y) x) = X0 := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e88 (M.op X0 y)
           grind)
        | exact superpose b0e88 b0e32
        | exact resolve b0e32 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e88
      have b0e3202 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 y) y)) x) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e233 X1 (M.op (M.op X0 y) y) x
           have i₂ := b0e851 X0
           grind)
        | exact superpose b0e851 b0e233
        | exact resolve b0e233 b0e851
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e851
      have b0e3355 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) x) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e3202 X0 X1
           have i₂ := b0e347 (M.op X1 X0) X0 y
           grind)
        | exact superpose b0e347 b0e3202
        | exact resolve b0e3202 b0e347
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e347 b0e3202
      have b0e4318 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 x) := by
        intro X0 X1
        first
        | (have i₁ := b0e3355 X1 (M.op X0 (M.op X1 X1))
           have i₂ := b0e233 X0 X1 X1
           grind)
        | exact superpose b0e233 b0e3355
        | exact resolve b0e3355 b0e233
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e233
      have b0e4336 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X2) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e440 (M.op (M.op X0 X2) X2) X1
           have i₂ := b0e3355 X2 X0
           grind)
        | exact superpose b0e3355 b0e440
        | exact resolve b0e440 b0e3355
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e440 b0e3355
      have b0e6719 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e4318 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e4318
        | exact resolve b0e4318 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e7554 : (σ (M.op y x)) = (M.op (σ y) x) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e6719 (σ y)
           grind)
        | exact superpose b0e6719 b0e44
        | exact resolve b0e44 b0e6719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e6719
      have b0e68280 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) X0) := by
        intro X0
        first
        | (have i₁ := b0e4336 (σ y) X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e4336
        | exact resolve b0e4336 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4336
      have b0e445560 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e703 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e703
      have b0e445562 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e445560 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445560
      have b0e445563 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e445562 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445562
      have b0e445611 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e127 X0 X0
           have i₂ := b0e445563 (τ X0)
           grind)
        | exact superpose b0e445563 b0e127
        | exact resolve b0e127 b0e445563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e445617 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e445611 X0
           have i₂ := b0e445563 X0
           grind)
        | exact superpose b0e445563 b0e445611
        | exact resolve b0e445611 b0e445563
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445563 b0e445611
      have b0e446396 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (k (τ (M.op X0 X0)) (τ X0)) := by
        intro X0
        grind
      have b0e446425 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X1 (τ (M.op X0 X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e4318 X1 (τ X0)
           have i₂ := b0e445617 X0
           grind)
        | exact superpose b0e445617 b0e4318
        | exact resolve b0e4318 b0e445617
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e445617
      have b0e446715 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (k (M.op X0 X0) X0)) := by
        intro X0
        first
        | (have i₁ := b0e446396 X0
           have i₂ := b0e127 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e127 b0e446396
        | exact resolve b0e446396 b0e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e127 b0e446396
      have b0e446834 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 (M.op X0 X0))) := by
        intro X0
        grind
      clear b0e446715
      have b0e446919 : ∀ X0 : G, (M.op (τ X0) (τ (M.op X0 X0))) = (τ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e446834 X0
           have i₂ := b0e4318 X0 X0
           grind)
        | exact superpose b0e4318 b0e446834
        | exact resolve b0e446834 b0e4318
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4318 b0e446834
      have b0e446987 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e446919 X0
           have i₂ := b0e446425 X0 (τ X0)
           grind)
        | exact superpose b0e446425 b0e446919
        | exact resolve b0e446919 b0e446425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e446425 b0e446919
      have b0e447983 : ∀ X0 : G, (M.op X0 x) = (σ (M.op (τ X0) x)) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op X0 x)
           have i₂ := b0e446987 X0
           grind)
        | exact superpose b0e446987 b0e13
        | exact resolve b0e13 b0e446987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e446987
      have b0e451828 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
        intro X0
        first
        | (have i₁ := b0e447983 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e447983
        | exact resolve b0e447983 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e447983
      have b0e453600 : (σ (M.op x y)) = (M.op (σ (M.op y x)) x) := by
        first
        | (have i₁ := b0e451828 (M.op y x)
           have i₂ := b0e502 x
           grind)
        | exact superpose b0e502 b0e451828
        | exact resolve b0e451828 b0e502
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e502 b0e451828
      have b0e453774 : (σ (M.op x y)) = (M.op (M.op (σ y) x) x) := by
        first
        | (have i₁ := b0e453600
           have i₂ := b0e7554
           grind)
        | exact superpose b0e7554 b0e453600
        | exact resolve b0e453600 b0e7554
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7554 b0e453600
      have b0e453825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e453774
           have i₂ := b0e68280 x
           grind)
        | exact superpose b0e68280 b0e453774
        | exact resolve b0e453774 b0e68280
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68280 b0e453774
      have b0e453850 : False := by grind
      exact b0e453850
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : x = (M.op y y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 y)) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 y y X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
             have i₂ := b1e12 X0 X3 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (k x y) = (M.op y x) := by grind
        have b1e40 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
        have b1e41 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e43 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e47 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b1e48 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e43
             have r₂ := b1e21
             grind)
          | exact resolve b1e43 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e49 : (σ x) = (σ (k x y)) := by
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
        have b1e50 : (σ x) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e49
          | exact resolve b1e49 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e49
        have b1e53 : (M.op y x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op y x)
             have i₂ := b1e50
             grind)
          | exact superpose b1e50 b1e13
          | exact resolve b1e13 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e54 : x = (M.op y x) := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e53
          | exact resolve b1e53 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b1e87 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x y
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e12
          | exact resolve b1e12 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e88 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 y x X0
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e12
          | exact resolve b1e12 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e91 : ∀ X0 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 x) y) := by
          intro X0
          first
          | (have i₁ := b1e30 (M.op (M.op X0 y) x)
             have i₂ := b1e30 X0
             grind)
          | exact superpose b1e30 b1e30
          | exact resolve b1e30 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e122 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e87 (M.op (M.op X0 X1) (M.op x X1))
             have i₂ := b1e12 X0 X1 x
             grind)
          | exact superpose b1e12 b1e87
          | exact resolve b1e87 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e132 : ∀ X0 X1 : G, (M.op (M.op X0 y) x) = (M.op (M.op X0 X1) (M.op x X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e122 X0 X1
             have i₂ := b1e91 X0
             grind)
          | exact superpose b1e91 b1e122
          | exact resolve b1e122 b1e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e134 : (σ (M.op x y)) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e41
             grind)
          | exact superpose b1e41 b1e19
          | exact resolve b1e19 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e150 : (M.op (M.op y x) y) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b1e30 (M.op x (M.op y x))
             have i₂ := b1e88 y
             grind)
          | exact superpose b1e88 b1e30
          | exact resolve b1e30 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88
        have b1e153 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b1e150
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e150
          | exact resolve b1e150 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e150
        have b1e304 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 x X2
             have i₂ := b1e29 X0 x X2 X1
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e322 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) x) y) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e87 (M.op X0 (M.op x X2))
             have i₂ := b1e29 X0 X1 X2 x
             grind)
          | exact superpose b1e29 b1e87
          | exact resolve b1e87 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e87
        have b1e323 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) x) y) = (M.op X0 (M.op y X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 (M.op X0 (M.op y X2))
             have i₂ := b1e29 X0 X1 X2 y
             grind)
          | exact superpose b1e29 b1e30
          | exact resolve b1e30 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e325 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) y) x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e323 X0 X1 X2
             have i₂ := b1e91 (M.op (M.op X0 X1) (M.op X2 X1))
             grind)
          | exact superpose b1e91 b1e323
          | exact resolve b1e323 b1e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e323
        have b1e326 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) y) x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e322 X0 X1 X2
             have i₂ := b1e91 (M.op (M.op X0 X1) (M.op X2 X1))
             grind)
          | exact superpose b1e91 b1e322
          | exact resolve b1e322 b1e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91 b1e322
        have b1e357 : ∀ X0 X2 : G, (M.op X0 (M.op x X2)) = (M.op X0 (M.op y X2)) := by
          intro X0 X2
          first
          | (have i₁ := b1e326 X0 x X2
             have i₂ := b1e325 X0 x X2
             grind)
          | exact superpose b1e325 b1e326
          | exact resolve b1e326 b1e325
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e325 b1e326
        have b1e398 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y X1) (M.op x X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e32 y (M.op X0 y) x X1
             have i₂ := b1e30 X0
             grind)
          | exact superpose b1e30 b1e32
          | exact resolve b1e32 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e447 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op X1 x) (M.op x y))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e32 X1 X0 x x
             have i₂ := b1e153
             grind)
          | exact superpose b1e153 b1e32
          | exact resolve b1e32 b1e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e459 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
             have i₂ := b1e32 (M.op X1 X2) X0 X1 X2
             grind)
          | exact superpose b1e32 b1e12
          | exact resolve b1e12 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e481 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op X1 x) (M.op y y))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e447 X0 X1
             have i₂ := b1e357 (M.op X1 x) y
             grind)
          | exact superpose b1e357 b1e447
          | exact resolve b1e447 b1e357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e447
        have b1e507 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op (M.op y y) x)) := by
          intro X0
          first
          | (have i₁ := b1e398 X0 x
             have i₂ := b1e132 y x
             grind)
          | exact superpose b1e132 b1e398
          | exact resolve b1e398 b1e132
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e132 b1e398
        have b1e526 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op X1 x) x)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e481 X0 X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e481
          | exact resolve b1e481 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e481
        have b1e541 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op x x)) := by
          intro X0
          first
          | (have i₁ := b1e507 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e507
          | exact resolve b1e507 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e507
        have b1e548 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e526 X0 X1
             have i₂ := b1e459 (M.op (M.op X0 x) X1) X1 x
             grind)
          | exact superpose b1e459 b1e526
          | exact resolve b1e526 b1e459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e526
        have b1e558 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b1e541 X0
             have i₂ := b1e357 X0 x
             grind)
          | exact superpose b1e357 b1e541
          | exact resolve b1e541 b1e357
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e357 b1e541
        have b1e567 : ∀ X0 : G, (M.op X0 y) = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b1e558 X0
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e558
          | exact resolve b1e558 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54 b1e558
        have b1e589 : ∀ X0 : G, (M.op (M.op (M.op X0 y) y) y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e30 X0
             have i₂ := b1e567 (M.op X0 y)
             grind)
          | exact superpose b1e567 b1e30
          | exact resolve b1e30 b1e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30
        have b1e686 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op (M.op X0 y) y)) := by
          intro X0
          first
          | (have i₁ := b1e27 (M.op (M.op X0 y) y)
             have i₂ := b1e589 X0
             grind)
          | exact superpose b1e589 b1e27
          | exact resolve b1e27 b1e589
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e589
        have b1e697 : ∀ X0 : G, y = (M.op (M.op x X0) X0) := by
          intro X0
          first
          | (have i₁ := b1e686 X0
             have i₂ := b1e459 (M.op x X0) X0 y
             grind)
          | exact superpose b1e459 b1e686
          | exact resolve b1e686 b1e459
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e459 b1e686
        have b1e822 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b1e47 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e1065 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X2) = (M.op (M.op X0 x) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op (M.op X0 x) X1) X1 X2
             have i₂ := b1e548 X0 X1
             grind)
          | exact superpose b1e548 b1e12
          | exact resolve b1e12 b1e548
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e548
        have b1e1093 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X2) = (M.op (M.op X0 y) X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e1065 X0 X1 X2
             have i₂ := b1e567 X0
             grind)
          | exact superpose b1e567 b1e1065
          | exact resolve b1e1065 b1e567
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e567 b1e1065
        have b1e4131 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e83 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e83
          | exact resolve b1e83 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83
        have b1e4394 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b1e4131
        have b1e5504 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op X3 X2)) X3) = X0 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e29 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2 X3
             have i₂ := b1e304 X0 X1 (M.op X2 X1)
             grind)
          | exact superpose b1e304 b1e29
          | exact resolve b1e29 b1e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e5505 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
             have i₂ := b1e304 X0 X1 (M.op X2 X1)
             grind)
          | exact superpose b1e304 b1e12
          | exact resolve b1e12 b1e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e304
        have b1e5580 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X1))) y) X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e5504 X0 X1 X2 x
             have i₂ := b1e1093 (M.op X0 (M.op X1 (M.op X2 X1))) X2 x
             grind)
          | exact superpose b1e1093 b1e5504
          | exact resolve b1e5504 b1e1093
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1093 b1e5504
        have b1e5641 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X2) y) X2) = X0 := by
          intro X0 X2
          first
          | (have i₁ := b1e5580 X0 x X2
             have i₂ := b1e5505 X0 x X2
             grind)
          | exact superpose b1e5505 b1e5580
          | exact resolve b1e5580 b1e5505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5505 b1e5580
        have b1e6077 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X1 y)) y X1
             have i₂ := b1e5641 X0 (M.op X1 y)
             grind)
          | exact superpose b1e5641 b1e12
          | exact resolve b1e12 b1e5641
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e7541 : y = (M.op (M.op y y) y) ∨ y = (k y (M.op y y)) := by grind
        clear b1e6077
        have b1e7594 : y = (k y (M.op y y)) := by
          first
          | (have j1 := b1e822 y
             grind)
          | (have r₁ := b1e7541
             have r₂ := b1e822 y
             grind)
          | exact resolve b1e7541 b1e822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e822 b1e7541
        have b1e7662 : y = (k y x) := by
          first
          | (have i₁ := b1e7594
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e7594
          | exact resolve b1e7594 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7594
        have b1e8164 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e134
             have i₂ := b1e7662
             grind)
          | exact superpose b1e7662 b1e134
          | exact resolve b1e134 b1e7662
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e134 b1e7662
        have b1e9275 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e4394
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e4394
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e4394 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4394
        have b1e9293 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
        clear b1e9275
        have b1e9311 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e9293
             have i₂ := b1e153
             grind)
          | exact superpose b1e153 b1e9293
          | exact resolve b1e9293 b1e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9293
        have b1e9323 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b1e9311
             have r₂ := b1e8164
             grind)
          | exact resolve b1e9311 b1e8164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e9311
        have b1e9333 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e9323
             have i₂ := b1e153
             grind)
          | exact superpose b1e153 b1e9323
          | exact resolve b1e9323 b1e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153 b1e9323
        have b1e19097 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e5641 x y
             have i₂ := b1e9333
             grind)
          | exact superpose b1e9333 b1e5641
          | exact resolve b1e5641 b1e9333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e5641 b1e9333
        have b1e19098 : (σ x) = (σ y) ∨ x = y := by
          first
          | (have i₁ := b1e19097
             have i₂ := b1e697 y
             grind)
          | exact superpose b1e697 b1e19097
          | exact resolve b1e19097 b1e697
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e697 b1e19097
        have b1e19423 : x = (τ (σ y)) ∨ x = y := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e19098
             grind)
          | exact superpose b1e19098 b1e13
          | exact resolve b1e13 b1e19098
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19098
        have b1e19440 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e19423
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e19423
          | exact resolve b1e19423 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19423
        have b1e19441 : x = y := by grind
        clear b1e19440
        have b1e19784 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e8164
             have i₂ := b1e19441
             grind)
          | exact superpose b1e19441 b1e8164
          | exact resolve b1e8164 b1e19441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8164
        have b1e19789 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e19784
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e19784
          | exact resolve b1e19784 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19784
        have b1e19817 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e19789
             have i₂ := b1e19441
             grind)
          | exact superpose b1e19441 b1e19789
          | exact resolve b1e19789 b1e19441
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e19441 b1e19789
        have b1e19818 : False := by grind
        exact b1e19818
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e37 : (k x y) = (M.op y x) := by grind
        have b2e42 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b2e61 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e66 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b2e463 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b2e42 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e585 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e61 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e586 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e585
             have r₂ := b2e22
             grind)
          | exact resolve b2e585 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e585
        have b2e587 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e586
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e586
          | exact resolve b2e586 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e586
        have b2e588 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b2e587
             have i₂ := b2e37
             grind)
          | exact superpose b2e37 b2e587
          | exact resolve b2e587 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37 b2e587
        have b2e695 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e66 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e696 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
          intro X0
          first
          | (have j0 := b2e695 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e695
        have b2e728 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e588
             grind)
          | exact superpose b2e588 b2e19
          | exact resolve b2e19 b2e588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e588
        have b2e2668 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e71 y y
             grind)
          | exact superpose b2e71 b2e21
          | (have j1 := b2e71 y y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e71 x y
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e71 y x
             grind)
          | exact resolve b2e21 b2e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e2817 : (σ x) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b2e2668
        have b2e31567 : (σ x) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e2817
             have i₂ := b2e696 y
             grind)
          | exact superpose b2e696 b2e2817
          | (have j1 := b2e696 (σ y)
             grind)
          | exact resolve b2e2817 b2e696
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2817
        have b2e31569 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e31567
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31567
          | exact resolve b2e31567 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31567
        have b2e31570 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
        clear b2e31569
        have b2e31587 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e31570
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31570
          | exact resolve b2e31570 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31570
        have b2e31620 : (σ x) ≠ (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e31587
             grind)
          | exact superpose b2e31587 b2e21
          | exact resolve b2e21 b2e31587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31646 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e463 (σ y)
             have i₂ := b2e31587
             grind)
          | exact superpose b2e31587 b2e463
          | exact resolve b2e463 b2e31587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e463
        have b2e31724 : (σ y) = (k (σ y) (σ y)) ∨ x = y := by
          first
          | (have r₁ := b2e31646
             have r₂ := b2e31587
             grind)
          | exact resolve b2e31646 b2e31587
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31587 b2e31646
        have b2e31754 : (σ y) = (σ (k y y)) ∨ x = y := by
          first
          | (have i₁ := b2e31724
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e31724
          | exact resolve b2e31724 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31724
        have b2e34212 : (σ y) = (σ (M.op y y)) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e31754
             have i₂ := b2e696 y
             grind)
          | exact superpose b2e696 b2e31754
          | (have j1 := b2e696 y
             grind)
          | exact resolve b2e31754 b2e696
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e696 b2e31754
        have b2e34247 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e34212
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e34212
          | exact resolve b2e34212 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34212
        have b2e34257 : x = y ∨ y = (M.op y y) := by
          first
          | (have r₁ := b2e34247
             have r₂ := b2e31620
             grind)
          | exact resolve b2e34247 b2e31620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31620 b2e34247
        have b2e34267 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e34257
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e34257
          | exact resolve b2e34257 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34257
        have b2e34268 : x = y := by grind
        clear b2e34267
        have b2e36520 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e728
             have i₂ := b2e34268
             grind)
          | exact superpose b2e34268 b2e728
          | exact resolve b2e728 b2e34268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e728 b2e34268
        have b2e36545 : False := by grind
        exact b2e36545
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 x x X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) x) = X0 := by
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
        have b3e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
             have i₂ := b3e12 X0 X3 X2
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e35 : x = (M.op (M.op y x) (M.op y (M.op x x))) := by
          first
          | (have i₁ := b3e27 (M.op y (M.op x x))
             have i₂ := b3e27 x
             grind)
          | exact superpose b3e27 b3e27
          | exact resolve b3e27 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e38 : x = (M.op (M.op y x) (M.op y y)) := by
          first
          | (have i₁ := b3e35
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e35
          | exact resolve b3e35 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e35
        have b3e39 : (M.op x y) = (k y x) := by grind
        have b3e40 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        have b3e41 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e40
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e40
          | exact resolve b3e40 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e42 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
        have b3e48 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e43
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e43
          | exact resolve b3e43 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e49 : x = (k x y) := by
          first
          | (have r₁ := b3e42
             have r₂ := b3e20
             grind)
          | exact resolve b3e42 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e48
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e48
          | exact resolve b3e48 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e72 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b3e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b3e90 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op (M.op X0 x) y)) := by
          intro X0
          first
          | (have i₁ := b3e27 (M.op (M.op X0 x) y)
             have i₂ := b3e30 X0
             grind)
          | exact superpose b3e30 b3e27
          | exact resolve b3e27 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e231 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op y y) X1)) = (M.op (M.op X0 x) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e29 X0 X1 (M.op y y) (M.op y x)
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e29
          | exact resolve b3e29 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e312 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 x)) = (M.op (M.op x X1) (M.op (M.op X1 X2) (M.op X0 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e32 X1 (M.op y (M.op X0 x)) X0 X2
             have i₂ := b3e27 X0
             grind)
          | exact superpose b3e27 b3e32
          | exact resolve b3e32 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e316 : ∀ X0 X1 : G, (M.op y x) = (M.op (M.op x X0) (M.op (M.op X0 X1) (M.op (M.op y y) X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X0 (M.op y x) (M.op y y) X1
             have i₂ := b3e38
             grind)
          | exact superpose b3e38 b3e32
          | exact resolve b3e32 b3e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e373 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (M.op X1 (σ x)) (σ (k x y)))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X1 X0 (σ y) (σ x)
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e32
          | exact resolve b3e32 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e384 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
             have i₂ := b3e32 (M.op X1 X2) X0 X1 X2
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e406 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (M.op X1 (σ x)) (σ x))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e373 X0 X1
             have i₂ := b3e49
             grind)
          | exact superpose b3e49 b3e373
          | exact resolve b3e373 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e373
        have b3e424 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) (M.op (M.op X0 x) (M.op y x))) := by
          intro X0
          first
          | (have i₁ := b3e316 X0 x
             have i₂ := b3e231 X0 x
             grind)
          | exact superpose b3e231 b3e316
          | exact resolve b3e316 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e231 b3e316
        have b3e432 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e406 X0 X1
             have i₂ := b3e384 (M.op (M.op X0 (σ y)) X1) X1 (σ x)
             grind)
          | exact superpose b3e384 b3e406
          | exact resolve b3e406 b3e384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e406
        have b3e442 : (M.op y x) = (M.op y (M.op y x)) := by
          first
          | (have i₁ := b3e424 x
             have i₂ := b3e312 y x x
             grind)
          | exact superpose b3e312 b3e424
          | exact resolve b3e424 b3e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e312 b3e424
        have b3e462 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by grind
        clear b3e50
        have b3e476 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e462
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e462
          | exact resolve b3e462 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e462
        have b3e478 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
          first
          | (have i₁ := b3e476
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e476
          | exact resolve b3e476 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e476
        have b3e480 : (σ (M.op x y)) = (σ y) := by
          first
          | (have r₁ := b3e478
             have r₂ := b3e19
             grind)
          | exact resolve b3e478 b3e19
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e478
        have b3e485 : (M.op x y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op x y)
             have i₂ := b3e480
             grind)
          | exact superpose b3e480 b3e13
          | exact resolve b3e13 b3e480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e486 : y = (M.op x y) := by
          first
          | (have i₁ := b3e485
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e485
          | exact resolve b3e485 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e485
        have b3e552 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) (M.op (M.op X1 y) y)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X1 X0 x y
             have i₂ := b3e486
             grind)
          | exact superpose b3e486 b3e32
          | exact resolve b3e32 b3e486
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e486
        have b3e553 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 x) X1) X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e552 X0 X1
             have i₂ := b3e384 (M.op (M.op X0 x) X1) X1 y
             grind)
          | exact superpose b3e384 b3e552
          | exact resolve b3e552 b3e384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e552
        have b3e1043 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) (M.op (M.op X1 (M.op y x)) (M.op y x))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X1 X0 y (M.op y x)
             have i₂ := b3e442
             grind)
          | exact superpose b3e442 b3e32
          | exact resolve b3e32 b3e442
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e442
        have b3e1044 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X1) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1043 X0 X1
             have i₂ := b3e384 (M.op (M.op X0 y) X1) X1 (M.op y x)
             grind)
          | exact superpose b3e384 b3e1043
          | exact resolve b3e1043 b3e384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1043
        have b3e3731 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e76 y y
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e76
          | exact resolve b3e76 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e3998 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b3e3731
        have b3e5751 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e1044 (M.op X0 (σ y)) y
             have i₂ := b3e432 X0 y
             grind)
          | exact superpose b3e432 b3e1044
          | exact resolve b3e1044 b3e432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e432 b3e1044
        have b3e6515 : (σ x) = (M.op (σ y) y) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e5751 (σ y)
             grind)
          | exact superpose b3e5751 b3e22
          | exact resolve b3e22 b3e5751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e6516 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e5751 (σ x)
             grind)
          | exact superpose b3e5751 b3e19
          | exact resolve b3e19 b3e5751
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5751
        have b3e6528 : (σ y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b3e6516
             have i₂ := b3e480
             grind)
          | exact superpose b3e480 b3e6516
          | exact resolve b3e6516 b3e480
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e480 b3e6516
        have b3e6715 : ∀ X0 : G, x = (M.op (M.op y (M.op (M.op X0 x) x)) (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e90 (M.op (M.op X0 x) x)
             have i₂ := b3e553 X0 x
             grind)
          | exact superpose b3e553 b3e90
          | exact resolve b3e90 b3e553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90 b3e553
        have b3e6808 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e6715 X0
             have i₂ := b3e384 y X0 x
             grind)
          | exact superpose b3e384 b3e6715
          | exact resolve b3e6715 b3e384
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e384 b3e6715
        have b3e11743 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e3998
             grind)
          | exact superpose b3e3998 b3e13
          | exact resolve b3e13 b3e3998
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3998
        have b3e11761 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e11743
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e11743
          | exact resolve b3e11743 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e11743
        have b3e23912 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e72 y y
             have i₂ := b3e11761
             grind)
          | exact superpose b3e11761 b3e72
          | (have j0 := b3e72 y x
             grind)
          | exact resolve b3e72 b3e11761
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72 b3e11761
        have b3e23916 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b3e23912
        have b3e23925 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e23916
             have r₂ := b3e20
             grind)
          | exact resolve b3e23916 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23916
        have b3e24825 : x = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e6808 y
             have i₂ := b3e23925
             grind)
          | exact superpose b3e23925 b3e6808
          | exact resolve b3e6808 b3e23925
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6808 b3e23925
        have b3e24873 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e24825
             have r₂ := b3e20
             grind)
          | exact resolve b3e24825 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24825
        have b3e25176 : (σ y) ≠ (M.op (σ y) y) := by
          first
          | (have i₁ := b3e6528
             have i₂ := b3e24873
             grind)
          | exact superpose b3e24873 b3e6528
          | exact resolve b3e6528 b3e24873
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6528
        have b3e25213 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e25176
             have i₂ := b3e6515
             grind)
          | exact superpose b3e6515 b3e25176
          | exact resolve b3e25176 b3e6515
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6515 b3e25176
        have b3e25234 : False := by grind
        exact b3e25234
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e45 : (M.op x y) = (k y x) := by grind
          have b4e46 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          have b4e47 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b4e46
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e46
            | exact resolve b4e46 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e48 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e47
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e47
            | exact resolve b4e47 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e47
          have b4e49 : False := by grind
          exact b4e49
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
          have b5e33 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b5e13 x x X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 : G, x = (M.op (M.op y X0) (M.op (M.op X0 X1) (M.op x X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e33 (M.op (M.op X0 X1) (M.op x X1))
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e33
            | exact resolve b5e33 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op y (M.op X1 x))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op y (M.op X1 x))
               have i₂ := b5e33 X1
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y (M.op X0 x)) = (M.op (M.op x (M.op X1 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op y (M.op X0 x)) X0 X1
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e13
            | exact resolve b5e13 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b5e70 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b5e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b5e86 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op x X1)) = (M.op (M.op X0 y) x) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (M.op (M.op X0 X1) (M.op x X1))
               have i₂ := b5e13 X0 X1 x
               grind)
            | exact superpose b5e13 b5e35
            | exact resolve b5e35 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e89 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) x) := by
            intro X0
            first
            | (have i₁ := b5e35 (M.op (M.op X0 x) y)
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e35
            | exact resolve b5e35 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e92 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 (M.op X1 x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op (M.op X0 x) y) x X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 X1) (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e86 X0 X1
               have i₂ := b5e89 X0
               grind)
            | exact superpose b5e89 b5e86
            | exact resolve b5e86 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e106 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b5e28
          have b5e143 : ∀ X0 X1 X2 : G, (M.op x (M.op X1 X0)) = (M.op (M.op (M.op y (M.op X0 x)) (M.op X2 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 (M.op y (M.op X0 x)) X0 X1 X2
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) x) = (M.op (M.op X0 (M.op X2 (M.op y (M.op X1 x)))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 (M.op y (M.op X1 x)) X2
               have i₂ := b5e33 X1
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e157 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 (M.op X4 X2)) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34 X0 x X2 X4
               have i₂ := b5e34 X0 x X2 X1
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e164 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 x) (M.op y (M.op X2 x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 X2 (M.op y (M.op X2 x))
               have i₂ := b5e33 X2
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e168 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op x X2)) = (M.op (M.op X1 X0) (M.op (M.op X0 x) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X1 X2 x (M.op (M.op X0 x) y)
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e34
            | exact resolve b5e34 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e174 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op y (M.op (M.op X0 X1) x)) X2) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 (M.op y (M.op (M.op X0 X1) x)) X2 X1 X0
               have i₂ := b5e33 (M.op X0 X1)
               grind)
            | exact superpose b5e33 b5e34
            | exact resolve b5e34 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e181 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 X3) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X0 X1 X2 x
               have i₂ := b5e34 X0 X3 X2 x
               grind)
            | exact superpose b5e34 b5e34
            | exact resolve b5e34 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e182 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 x X2
               have i₂ := b5e34 X0 x X2 X1
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e183 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) X1) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          have b5e191 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e33 x
               have i₂ := b5e34 y X0 x x
               grind)
            | exact superpose b5e34 b5e33
            | exact resolve b5e33 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e192 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 x
               have i₂ := b5e34 (M.op X0 X1) X2 X1 x
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e195 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) y) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35 (M.op X0 (M.op x X2))
               have i₂ := b5e34 X0 X1 X2 x
               grind)
            | exact superpose b5e34 b5e35
            | exact resolve b5e35 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e197 : ∀ X0 X1 X2 : G, (M.op X0 (M.op x X2)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X1)) x) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e195 X0 X1 X2
               have i₂ := b5e89 (M.op (M.op X0 X1) (M.op X2 X1))
               grind)
            | exact superpose b5e89 b5e195
            | exact resolve b5e195 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e195
          have b5e198 : x = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b5e191 x
               have i₂ := b5e95 y x
               grind)
            | exact superpose b5e95 b5e191
            | exact resolve b5e191 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e191
          have b5e204 : ∀ X0 X1 : G, (M.op (M.op X1 x) y) = (M.op (M.op X1 X0) (M.op (M.op X0 x) y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e168 X0 X1 x
               have i₂ := b5e95 X1 x
               grind)
            | exact superpose b5e95 b5e168
            | exact resolve b5e168 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168
          have b5e210 : ∀ X0 : G, (M.op y x) = (M.op (M.op x (M.op X0 y)) X0) := by
            intro X0
            first
            | (have i₁ := b5e13 (M.op y x) y X0
               have i₂ := b5e198
               grind)
            | exact superpose b5e198 b5e13
            | exact resolve b5e13 b5e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e211 : (M.op y x) = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b5e210 x
               have i₂ := b5e41 y x
               grind)
            | exact superpose b5e41 b5e210
            | exact resolve b5e210 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e210
          have b5e228 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X2 X3) (M.op (M.op X2 X1) X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 (M.op X0 X1) (M.op X2 X1) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e36
            | exact resolve b5e36 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e229 : ∀ X0 X1 : G, y = (M.op x (M.op (M.op X0 X1) (M.op (M.op X0 x) X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 X0 y (M.op X0 x) X1
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e36
            | exact resolve b5e36 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e263 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) X0) = X1 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          have b5e272 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
               have i₂ := b5e36 (M.op X1 X2) X0 X1 X2
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e384 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) (M.op (M.op X1 (M.op y x)) (M.op y x))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e36 X1 X0 y (M.op y x)
               have i₂ := b5e211
               grind)
            | exact superpose b5e211 b5e36
            | exact resolve b5e36 b5e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e211
          have b5e385 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 y) X1) X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e384 X0 X1
               have i₂ := b5e272 (M.op (M.op X0 y) X1) X1 (M.op y x)
               grind)
            | exact superpose b5e272 b5e384
            | exact resolve b5e384 b5e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e384
          have b5e462 : ∀ X0 : G, (M.op y x) = (M.op (M.op x X0) X0) := by
            intro X0
            first
            | (have i₁ := b5e385 (M.op y x) X0
               have i₂ := b5e198
               grind)
            | exact superpose b5e198 b5e385
            | exact resolve b5e385 b5e198
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e198
          have b5e471 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X2) = (M.op (M.op X0 y) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op (M.op X0 y) X1) X1 X2
               have i₂ := b5e385 X0 X1
               grind)
            | exact superpose b5e385 b5e13
            | exact resolve b5e13 b5e385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e494 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b5e48 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e706 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e70 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e707 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b5e706 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e706
          have b5e1946 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op (M.op (M.op X0 X1) (M.op y X1)) x) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e89 (M.op (M.op X0 X1) (M.op y X1))
               have i₂ := b5e13 X0 X1 y
               grind)
            | exact superpose b5e13 b5e89
            | exact resolve b5e89 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1960 : ∀ X0 : G, (M.op (M.op (M.op X0 x) x) y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e35 X0
               have i₂ := b5e89 (M.op X0 x)
               grind)
            | exact superpose b5e89 b5e35
            | exact resolve b5e35 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e1989 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b5e1946 X0 x
               have i₂ := b5e197 X0 x y
               grind)
            | exact superpose b5e197 b5e1946
            | exact resolve b5e1946 b5e197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e197 b5e1946
          have b5e2961 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e75 x x
               grind)
            | exact superpose b5e75 b5e24
            | (have j1 := b5e75 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e75 y x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e75 x y
               grind)
            | exact resolve b5e24 b5e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e3117 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e2961
          have b5e4686 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 x) x)) y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e182 X1 (M.op (M.op X0 x) x) y
               have i₂ := b5e1960 X0
               grind)
            | exact superpose b5e1960 b5e182
            | exact resolve b5e182 b5e1960
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1960
          have b5e4729 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op y x) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e182 (M.op x (M.op X0 X1)) X0 X1
               have i₂ := b5e462 (M.op X0 X1)
               grind)
            | exact superpose b5e462 b5e182
            | exact resolve b5e182 b5e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e462
          have b5e4733 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 y) (M.op X1 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e182 (M.op (M.op X0 y) (M.op X1 X2)) X1 X2
               have i₂ := b5e385 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e385 b5e182
            | exact resolve b5e182 b5e385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4743 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e182 (M.op (M.op X0 X1) (M.op (M.op X2 X3) X1)) X2 X3
               have i₂ := b5e13 X0 X1 (M.op X2 X3)
               grind)
            | exact superpose b5e13 b5e182
            | exact resolve b5e182 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4755 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op (M.op X1 X2) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e182 (M.op X0 (M.op (M.op X1 X2) X1)) X1 X2
               have i₂ := b5e182 X0 (M.op X1 X2) X1
               grind)
            | exact superpose b5e182 b5e182
            | exact resolve b5e182 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4771 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e385 (M.op X0 (M.op y X1)) X1
               have i₂ := b5e182 X0 y X1
               grind)
            | exact superpose b5e182 b5e385
            | exact resolve b5e385 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e385
          have b5e4774 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X2 X3) (M.op X1 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36 X2 (M.op X0 (M.op X1 X2)) X1 X3
               have i₂ := b5e182 X0 X1 X2
               grind)
            | exact superpose b5e182 b5e36
            | exact resolve b5e36 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e4776 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X1))) (M.op X3 X2)) X3) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2 X3
               have i₂ := b5e182 X0 X1 (M.op X2 X1)
               grind)
            | exact superpose b5e182 b5e34
            | exact resolve b5e34 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4777 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op X0 (M.op X1 (M.op X2 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (M.op X0 (M.op X1 (M.op X2 X1))) X1 X2
               have i₂ := b5e182 X0 X1 (M.op X2 X1)
               grind)
            | exact superpose b5e182 b5e13
            | exact resolve b5e13 b5e182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e4836 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 (M.op X2 X1))) y) X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4776 X0 X1 X2 x
               have i₂ := b5e471 (M.op X0 (M.op X1 (M.op X2 X1))) X2 x
               grind)
            | exact superpose b5e471 b5e4776
            | exact resolve b5e4776 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4776
          have b5e4866 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X0) X0) y) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e4686 X0 X1
               have i₂ := b5e272 (M.op X1 X0) X0 x
               grind)
            | exact superpose b5e272 b5e4686
            | exact resolve b5e4686 b5e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4686
          have b5e4888 : ∀ X0 X2 : G, (M.op (M.op (M.op X0 X2) y) X2) = X0 := by
            intro X0 X2
            first
            | (have i₁ := b5e4836 X0 x X2
               have i₂ := b5e4777 X0 x X2
               grind)
            | exact superpose b5e4777 b5e4836
            | exact resolve b5e4836 b5e4777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4836
          have b5e5335 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x y) X0) := by
            intro X0
            first
            | (have i₁ := b5e4888 (M.op y (M.op X0 x)) X0
               have i₂ := b5e33 X0
               grind)
            | exact superpose b5e33 b5e4888
            | exact resolve b5e4888 b5e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5340 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 y) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4888 (M.op (M.op X0 X1) (M.op X2 X1)) X2
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e4888
            | exact resolve b5e4888 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5387 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 (M.op X1 y)) y X1
               have i₂ := b5e4888 X0 (M.op X1 y)
               grind)
            | exact superpose b5e4888 b5e13
            | exact resolve b5e13 b5e4888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5406 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op X1 X2)) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e182 (M.op (M.op X0 (M.op X1 X2)) y) X1 X2
               have i₂ := b5e4888 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e4888 b5e182
            | exact resolve b5e182 b5e4888
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4888
          have b5e5670 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op X4 X3)) X4) = (M.op X0 (M.op X3 (M.op X1 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 (M.op (M.op X0 X1) X2) (M.op X1 X2) X3 X4
               have i₂ := b5e192 X0 X1 X2
               grind)
            | exact superpose b5e192 b5e34
            | exact resolve b5e34 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5671 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op X4 (M.op (M.op X0 X2) X3))) X4) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X1 (M.op X2 X3) (M.op (M.op X0 X2) X3) X4
               have i₂ := b5e192 X0 X2 X3
               grind)
            | exact superpose b5e192 b5e34
            | exact resolve b5e34 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5672 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X3) X4)) = (M.op (M.op X1 X2) (M.op (M.op X3 X4) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X1 X2 (M.op X3 X4) (M.op (M.op X0 X3) X4)
               have i₂ := b5e192 X0 X3 X4
               grind)
            | exact superpose b5e192 b5e34
            | exact resolve b5e34 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e5688 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X3) X4)) = (M.op (M.op X1 X3) X4) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e5672 X0 X1 x X3 X4
               have i₂ := b5e4743 X1 x X3 X4
               grind)
            | exact superpose b5e4743 b5e5672
            | exact resolve b5e5672 b5e4743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5672
          have b5e5689 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 y) (M.op (M.op X0 X2) X3)) = (M.op (M.op X1 (M.op X2 X3)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e5671 X0 X1 X2 X3 x
               have i₂ := b5e471 X1 (M.op (M.op X0 X2) X3) x
               grind)
            | exact superpose b5e471 b5e5671
            | exact resolve b5e5671 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5671
          have b5e5690 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) X2) y) X3) = (M.op X0 (M.op X3 (M.op X1 X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e5670 X0 X1 X2 X3 x
               have i₂ := b5e471 (M.op (M.op X0 X1) X2) X3 x
               grind)
            | exact superpose b5e471 b5e5670
            | exact resolve b5e5670 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5670
          have b5e5824 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X3)) X0) = (M.op (M.op X1 (M.op X0 X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e5689 X0 X1 X2 X3
               have i₂ := b5e4733 X1 (M.op X0 X2) X3
               grind)
            | exact superpose b5e4733 b5e5689
            | exact resolve b5e5689 b5e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5689
          have b5e6061 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X2) X3)) = (M.op X1 (M.op X0 (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e272 X1 (M.op (M.op X0 X2) X3) (M.op X2 X3)
               have i₂ := b5e192 X0 X2 X3
               grind)
            | exact superpose b5e192 b5e272
            | exact resolve b5e272 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e192
          have b5e6067 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e272 X3 (M.op X0 (M.op X4 X2)) X4
               have i₂ := b5e34 X0 X1 X2 X4
               grind)
            | exact superpose b5e34 b5e272
            | exact resolve b5e272 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6229 : ∀ X0 : G, x = (M.op (M.op y X0) (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e33 (M.op X0 x)
               have i₂ := b5e272 y X0 x
               grind)
            | exact superpose b5e272 b5e33
            | exact resolve b5e33 b5e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e6347 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op (M.op (M.op X0 y) X2) X4)) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e6067 X0 x X2 X3 X4
               have i₂ := b5e5340 X0 x X2
               grind)
            | exact superpose b5e5340 b5e6067
            | exact resolve b5e6067 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6067
          have b5e6428 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op (M.op X0 y) (M.op X2 X4))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e6347 X0 X2 X3 X4
               have i₂ := b5e6061 (M.op X0 y) X3 X2 X4
               grind)
            | exact superpose b5e6061 b5e6347
            | exact resolve b5e6347 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6347
          have b5e6458 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X0 (M.op y (M.op X2 X4)))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e6428 X0 X2 X3 X4
               have i₂ := b5e6061 X0 X3 y (M.op X2 X4)
               grind)
            | exact superpose b5e6061 b5e6428
            | exact resolve b5e6428 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6428
          have b5e6475 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X0 (M.op X2 X4))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e6458 X0 X2 X3 X4
               have i₂ := b5e4771 X0 (M.op X2 X4)
               grind)
            | exact superpose b5e4771 b5e6458
            | exact resolve b5e6458 b5e4771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6458
          have b5e6530 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x X0) x) := by
            intro X0
            first
            | (have i₁ := b5e182 (M.op y X0) X0 x
               have i₂ := b5e6229 X0
               grind)
            | exact superpose b5e6229 b5e182
            | exact resolve b5e182 b5e6229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e6541 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op y X2)) = (M.op (M.op X0 X1) (M.op (M.op X2 x) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 (M.op X2 x) (M.op y X2)
               have i₂ := b5e6229 X2
               grind)
            | exact superpose b5e6229 b5e34
            | exact resolve b5e34 b5e6229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6229
          have b5e6569 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) (M.op y X2)) := by
            intro X0 X2
            first
            | (have i₁ := b5e6541 X0 x X2
               have i₂ := b5e4743 X0 x X2 x
               grind)
            | exact superpose b5e4743 b5e6541
            | exact resolve b5e6541 b5e4743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6541
          have b5e6613 : ∀ X0 X2 : G, (M.op (M.op X0 X2) x) = (M.op (M.op X0 x) X2) := by
            intro X0 X2
            first
            | (have i₁ := b5e6569 X0 X2
               have i₂ := b5e4771 (M.op X0 x) X2
               grind)
            | exact superpose b5e4771 b5e6569
            | exact resolve b5e6569 b5e4771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6569
          have b5e7649 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op y (M.op X2 x))) X0) = (M.op (M.op X1 (M.op X3 (M.op (M.op X0 X2) x))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 X1 (M.op y (M.op X2 x)) (M.op (M.op X0 X2) x) X3
               have i₂ := b5e40 X0 X2
               grind)
            | exact superpose b5e40 b5e34
            | exact resolve b5e34 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e7684 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op y (M.op X2 x))) X0) = (M.op (M.op X1 y) (M.op (M.op X0 X2) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e7649 X0 X1 X2 x
               have i₂ := b5e471 X1 (M.op (M.op X0 X2) x) x
               grind)
            | exact superpose b5e471 b5e7649
            | exact resolve b5e7649 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7649
          have b5e7811 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op y (M.op X2 x))) X0) = (M.op (M.op X1 (M.op X0 X2)) x) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e7684 X0 X1 X2
               have i₂ := b5e4733 X1 (M.op X0 X2) x
               grind)
            | exact superpose b5e4733 b5e7684
            | exact resolve b5e7684 b5e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7684
          have b5e7900 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op y (M.op X2 x))) X0) = (M.op (M.op X1 x) (M.op X0 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e7811 X0 X1 X2
               have i₂ := b5e6613 X1 (M.op X0 X2)
               grind)
            | exact superpose b5e6613 b5e7811
            | exact resolve b5e7811 b5e6613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6613 b5e7811
          have b5e7940 : ∀ X0 X1 X2 : G, (M.op (M.op X1 x) (M.op X0 X2)) = (M.op (M.op X1 (M.op X2 x)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e7900 X0 X1 X2
               have i₂ := b5e4771 X1 (M.op X2 x)
               grind)
            | exact superpose b5e4771 b5e7900
            | exact resolve b5e7900 b5e4771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7900
          have b5e9375 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op (M.op X3 x) X2)) x) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e92 (M.op X0 (M.op (M.op X3 x) X2)) X3
               have i₂ := b5e34 X0 X1 X2 (M.op X3 x)
               grind)
            | exact superpose b5e34 b5e92
            | exact resolve b5e92 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9531 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 (M.op x (M.op X3 x))) X2) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e9375 X0 X1 X2 X3
               have i₂ := b5e5824 x X0 (M.op X3 x) X2
               grind)
            | (have i₁ := b5e9375 X1 X1 X2 X3
               have i₂ := b5e5824 (M.op X3 x) X1 X2 x
               grind)
            | exact superpose b5e5824 b5e9375
            | exact resolve b5e9375 b5e5824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9375
          have b5e9627 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X3) = (M.op (M.op (M.op X0 X3) X2) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e9531 X0 X1 X2 X3
               have i₂ := b5e4777 X0 x X3
               grind)
            | exact superpose b5e4777 b5e9531
            | exact resolve b5e9531 b5e4777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9531
          have b5e9667 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 y) X2) X3) = (M.op (M.op (M.op X0 X3) X2) y) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e9627 X0 x X2 X3
               have i₂ := b5e5340 X0 x X2
               grind)
            | exact superpose b5e5340 b5e9627
            | exact resolve b5e9627 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9627
          have b5e10118 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x X3)) = (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e95 (M.op X0 (M.op X3 X2)) X3
               have i₂ := b5e34 X0 X1 X2 X3
               grind)
            | exact superpose b5e34 b5e95
            | exact resolve b5e95 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e10253 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X2)) X3) = (M.op (M.op (M.op X0 x) y) (M.op X2 (M.op x X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e34 (M.op X0 X1) (M.op x X1) X2 X3
               have i₂ := b5e95 X0 X1
               grind)
            | exact superpose b5e95 b5e34
            | exact resolve b5e34 b5e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e10296 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X3 X2)) X3) = (M.op (M.op (M.op X0 x) X2) (M.op x X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e10253 X0 X1 X2 X3
               have i₂ := b5e4733 (M.op X0 x) X2 (M.op x X1)
               grind)
            | exact superpose b5e4733 b5e10253
            | exact resolve b5e10253 b5e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10253
          have b5e10396 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x X3)) = (M.op (M.op (M.op X0 y) x) (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e10118 X0 X1 X2 X3
               have i₂ := b5e9667 X0 x (M.op X3 X2)
               grind)
            | exact superpose b5e9667 b5e10118
            | exact resolve b5e10118 b5e9667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10118
          have b5e10440 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) y) X2) = (M.op (M.op (M.op X0 x) X2) (M.op x X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e10296 X0 X1 X2 x
               have i₂ := b5e471 (M.op X0 X1) X2 x
               grind)
            | exact superpose b5e471 b5e10296
            | exact resolve b5e10296 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10296
          have b5e10519 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x X3)) = (M.op (M.op (M.op X0 x) y) (M.op X3 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e10396 X0 X1 X2 X3
               have i₂ := b5e89 X0
               grind)
            | exact superpose b5e89 b5e10396
            | exact resolve b5e10396 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10396
          have b5e10585 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) (M.op x X3)) = (M.op (M.op (M.op X0 x) X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e10519 X0 X1 X2 X3
               have i₂ := b5e4733 (M.op X0 x) X3 X2
               grind)
            | exact superpose b5e4733 b5e10519
            | exact resolve b5e10519 b5e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10519
          have b5e10632 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 x) X3) X2) = (M.op (M.op (M.op X0 y) X2) (M.op x X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e10585 X0 x X2 X3
               have i₂ := b5e5340 X0 x X2
               grind)
            | exact superpose b5e5340 b5e10585
            | exact resolve b5e10585 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10585
          have b5e11300 : ∀ X0 X1 X2 : G, (M.op y (M.op X1 X2)) = (M.op (M.op x X0) (M.op (M.op (M.op X1 x) X2) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 x X0 (M.op (M.op X1 x) X2) (M.op X1 X2)
               have i₂ := b5e229 X1 X2
               grind)
            | exact superpose b5e229 b5e34
            | exact resolve b5e34 b5e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229
          have b5e11348 : ∀ X1 X2 : G, (M.op y (M.op X1 X2)) = (M.op (M.op x (M.op X1 x)) X2) := by
            intro X1 X2
            first
            | (have i₁ := b5e11300 x X1 X2
               have i₂ := b5e4743 x x (M.op X1 x) X2
               grind)
            | exact superpose b5e4743 b5e11300
            | exact resolve b5e11300 b5e4743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11300
          have b5e11530 : ∀ X1 X2 : G, (M.op y (M.op X1 X2)) = (M.op (M.op x x) (M.op X2 X1)) := by
            intro X1 X2
            first
            | (have i₁ := b5e11348 X1 X2
               have i₂ := b5e7940 X2 x X1
               grind)
            | exact superpose b5e7940 b5e11348
            | exact resolve b5e11348 b5e7940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11348
          have b5e11691 : ∀ X1 X2 : G, (M.op y (M.op X2 X1)) = (M.op y (M.op X1 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b5e11530 X2 X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e11530
            | exact resolve b5e11530 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11530
          have b5e15296 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op y (M.op (M.op X1 X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e6530 (M.op (M.op X1 X0) X1)
               have i₂ := b5e4755 x X1 X0
               grind)
            | exact superpose b5e4755 b5e6530
            | exact resolve b5e6530 b5e4755
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4755
          have b5e15319 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op y (M.op X1 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15296 X0 X1
               have i₂ := b5e11691 X1 (M.op X1 X0)
               grind)
            | (have i₁ := b5e15296 X0 X1
               have i₂ := b5e11691 (M.op X1 X0) X1
               grind)
            | exact superpose b5e11691 b5e15296
            | exact resolve b5e15296 b5e11691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15296
          have b5e15523 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X1 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e15319 X0 X1
               have i₂ := b5e6530 X0
               grind)
            | exact superpose b5e6530 b5e15319
            | exact resolve b5e15319 b5e6530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6530 b5e15319
          have b5e16209 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 (M.op X0 (M.op X3 X2)) X3 X4 X5
               have i₂ := b5e157 X0 X3 X2 X1
               grind)
            | (have i₁ := b5e34 (M.op X0 (M.op X3 X2)) X3 X4 X5
               have i₂ := b5e157 X0 X1 X2 X3
               grind)
            | exact superpose b5e157 b5e34
            | exact resolve b5e34 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16231 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e272 X3 (M.op X0 (M.op X4 X2)) X4
               have i₂ := b5e157 X0 X4 X2 X1
               grind)
            | (have i₁ := b5e272 X3 (M.op X0 (M.op X4 X2)) X4
               have i₂ := b5e157 X0 X1 X2 X4
               grind)
            | exact superpose b5e157 b5e272
            | exact resolve b5e272 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e272
          have b5e16238 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X3 X4) X2)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e182 (M.op X0 (M.op (M.op X3 X4) X2)) X3 X4
               have i₂ := b5e157 X0 (M.op X3 X4) X2 X1
               grind)
            | (have i₁ := b5e182 (M.op X0 (M.op (M.op X3 X4) X2)) X3 X4
               have i₂ := b5e157 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b5e157 b5e182
            | exact resolve b5e182 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16241 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op (M.op X3 X4) X2)) X5) (M.op X4 X5)) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 (M.op X0 (M.op (M.op X3 X4) X2)) X5 X4 X3
               have i₂ := b5e157 X0 (M.op X3 X4) X2 X1
               grind)
            | (have i₁ := b5e34 (M.op X0 (M.op (M.op X3 X4) X2)) X5 X4 X3
               have i₂ := b5e157 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b5e157 b5e34
            | exact resolve b5e34 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e16242 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 (M.op (M.op X3 x) X2)) x) y) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e92 (M.op X0 (M.op (M.op X3 x) X2)) X3
               have i₂ := b5e157 X0 (M.op X3 x) X2 X1
               grind)
            | (have i₁ := b5e92 (M.op X0 (M.op (M.op X3 x) X2)) X3
               have i₂ := b5e157 X0 X1 X2 (M.op X3 x)
               grind)
            | exact superpose b5e157 b5e92
            | exact resolve b5e92 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e16299 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 y) x) (M.op (M.op X3 x) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16242 X0 X1 X2 X3
               have i₂ := b5e9667 X0 x (M.op (M.op X3 x) X2)
               grind)
            | exact superpose b5e9667 b5e16242
            | exact resolve b5e16242 b5e9667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16242
          have b5e16300 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op (M.op X3 X4) X2)) X5) (M.op X4 X5)) = (M.op (M.op (M.op X0 y) X2) X3) := by
            intro X0 X2 X3 X4 X5
            first
            | (have i₁ := b5e16241 X0 x X2 X3 X4 X5
               have i₂ := b5e471 X0 X2 x
               grind)
            | exact superpose b5e471 b5e16241
            | exact resolve b5e16241 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16241
          have b5e16303 : ∀ X0 X2 X3 X4 : G, (M.op X0 (M.op (M.op X3 X4) X2)) = (M.op (M.op (M.op (M.op X0 y) X2) X3) X4) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16238 X0 x X2 X3 X4
               have i₂ := b5e471 X0 X2 x
               grind)
            | exact superpose b5e471 b5e16238
            | exact resolve b5e16238 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16238
          have b5e16310 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X4))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e16231 X0 X1 X2 X3 X4
               have i₂ := b5e6061 (M.op X0 (M.op X1 X2)) X3 X1 X4
               grind)
            | exact superpose b5e6061 b5e16231
            | exact resolve b5e16231 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16231
          have b5e16332 : ∀ X0 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) (M.op X5 X4)) X5) = (M.op (M.op (M.op X0 y) X2) (M.op X4 X3)) := by
            intro X0 X2 X3 X4 X5
            first
            | (have i₁ := b5e16209 X0 x X2 X3 X4 X5
               have i₂ := b5e471 X0 X2 x
               grind)
            | exact superpose b5e471 b5e16209
            | exact resolve b5e16209 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16209
          have b5e16790 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 y) x) (M.op X3 (M.op x X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16299 X0 X1 X2 X3
               have i₂ := b5e6061 X3 (M.op (M.op X0 y) x) x X2
               grind)
            | exact superpose b5e6061 b5e16299
            | exact resolve b5e16299 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16299
          have b5e16791 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 y) X2) X3) = (M.op (M.op (M.op X0 (M.op (M.op X3 X4) X2)) y) X4) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16300 X0 X2 X3 X4 x
               have i₂ := b5e5340 (M.op X0 (M.op (M.op X3 X4) X2)) x X4
               grind)
            | exact superpose b5e5340 b5e16300
            | exact resolve b5e16300 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16300
          have b5e16794 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 y) X2) X3) X4) = (M.op X0 (M.op X3 (M.op X4 X2))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16303 X0 X2 X3 X4
               have i₂ := b5e6061 X3 X0 X4 X2
               grind)
            | exact superpose b5e6061 b5e16303
            | exact resolve b5e16303 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16303
          have b5e16800 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X4)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e16310 X0 X1 X2 X3 X4
               have i₂ := b5e6061 X0 X3 (M.op X1 X2) (M.op X1 X4)
               grind)
            | exact superpose b5e6061 b5e16310
            | exact resolve b5e16310 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16310
          have b5e16819 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 y) X2) (M.op X4 X3)) = (M.op (M.op (M.op X0 (M.op X3 X2)) y) X4) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16332 X0 X2 X3 X4 x
               have i₂ := b5e471 (M.op X0 (M.op X3 X2)) X4 x
               grind)
            | exact superpose b5e471 b5e16332
            | exact resolve b5e16332 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16332
          have b5e17075 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 x) y) (M.op X3 (M.op x X2))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e16790 X0 X1 X2 X3
               have i₂ := b5e89 X0
               grind)
            | exact superpose b5e89 b5e16790
            | exact resolve b5e16790 b5e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89 b5e16790
          have b5e17076 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 y) X2) X3) = (M.op (M.op (M.op X0 (M.op X3 X4)) X2) X4) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16791 X0 X2 X3 X4
               have i₂ := b5e5406 X0 (M.op X3 X4) X2
               grind)
            | exact superpose b5e5406 b5e16791
            | exact resolve b5e16791 b5e5406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16791
          have b5e17082 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X0 (M.op X1 (M.op X2 (M.op X1 X4))))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e16800 X0 X1 X2 X3 X4
               have i₂ := b5e6061 X1 X0 X2 (M.op X1 X4)
               grind)
            | exact superpose b5e6061 b5e16800
            | exact resolve b5e16800 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16800
          have b5e17097 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X0 y) X2) (M.op X4 X3)) = (M.op (M.op (M.op X0 X3) X2) X4) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e16819 X0 X2 X3 X4
               have i₂ := b5e5406 X0 X3 X2
               grind)
            | exact superpose b5e5406 b5e16819
            | exact resolve b5e16819 b5e5406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5406 b5e16819
          have b5e17238 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 x) X3) (M.op x X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17075 X0 X1 X2 X3
               have i₂ := b5e4733 (M.op X0 x) X3 (M.op x X2)
               grind)
            | exact superpose b5e4733 b5e17075
            | exact resolve b5e17075 b5e4733
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4733 b5e17075
          have b5e17324 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X3) = (M.op (M.op (M.op X0 X2) y) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e17238 X0 X1 X2 X3
               have i₂ := b5e10440 X0 X2 X3
               grind)
            | exact superpose b5e10440 b5e17238
            | exact resolve b5e17238 b5e10440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10440 b5e17238
          have b5e17358 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 y) X2) X3) = (M.op (M.op (M.op X0 X2) y) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e17324 X0 x X2 X3
               have i₂ := b5e471 X0 X2 x
               grind)
            | exact superpose b5e471 b5e17324
            | exact resolve b5e17324 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17324
          have b5e20098 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op (M.op X0 X1) (M.op X2 X1)))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e4777 X3 X4 (M.op X0 (M.op X4 X2))
               have i₂ := b5e34 X0 X1 X2 X4
               grind)
            | exact superpose b5e34 b5e4777
            | exact resolve b5e4777 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e20500 : ∀ X0 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X4 X2))) = (M.op X3 (M.op X4 (M.op X2 X0))) := by
            intro X0 X2 X3 X4
            first
            | (have i₁ := b5e20098 X0 x X2 X3 X4
               have i₂ := b5e4774 X4 X2 X0 x
               grind)
            | exact superpose b5e4774 b5e20098
            | exact resolve b5e20098 b5e4774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4774 b5e20098
          have b5e20863 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op (M.op X3 x) y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e204 X3 (M.op X0 (M.op X3 X2))
               have i₂ := b5e157 X0 X3 X2 X1
               grind)
            | (have i₁ := b5e204 X3 (M.op X0 (M.op X3 X2))
               have i₂ := b5e157 X0 X1 X2 X3
               grind)
            | exact superpose b5e157 b5e204
            | exact resolve b5e204 b5e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e157 b5e204
          have b5e21230 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X3 (M.op x y))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e20863 X0 X1 X2 X3
               have i₂ := b5e6061 X3 (M.op (M.op X0 (M.op X1 X2)) X1) x y
               grind)
            | exact superpose b5e6061 b5e20863
            | exact resolve b5e20863 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20863
          have b5e21436 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) = (M.op (M.op (M.op X0 (M.op X1 X2)) X1) (M.op X3 x)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e21230 X0 X1 X2 X3
               have i₂ := b5e1989 X3
               grind)
            | exact superpose b5e1989 b5e21230
            | exact resolve b5e21230 b5e1989
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1989 b5e21230
          have b5e21615 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) = (M.op (M.op (M.op X0 y) X2) (M.op X3 x)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e21436 X0 x X2 X3
               have i₂ := b5e471 X0 X2 x
               grind)
            | exact superpose b5e471 b5e21436
            | exact resolve b5e21436 b5e471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e471 b5e21436
          have b5e21719 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X3 X2)) x) y) = (M.op (M.op (M.op X0 x) X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e21615 X0 X2 X3
               have i₂ := b5e17097 X0 X2 x X3
               grind)
            | (have i₁ := b5e21615 X0 X2 X3
               have i₂ := b5e17097 X0 X2 y (M.op X3 x)
               grind)
            | exact superpose b5e17097 b5e21615
            | exact resolve b5e21615 b5e17097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21615
          have b5e21778 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 y) x) (M.op X3 X2)) = (M.op (M.op (M.op X0 x) X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e21719 X0 X2 X3
               have i₂ := b5e9667 X0 x (M.op X3 X2)
               grind)
            | exact superpose b5e9667 b5e21719
            | exact resolve b5e21719 b5e9667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21719
          have b5e21822 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X0 X2) x) X3) = (M.op (M.op (M.op X0 x) X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e21778 X0 X2 X3
               have i₂ := b5e17097 X0 x X2 X3
               grind)
            | (have i₁ := b5e21778 X0 X2 X3
               have i₂ := b5e17097 X0 x y (M.op X3 X2)
               grind)
            | exact superpose b5e17097 b5e21778
            | exact resolve b5e21778 b5e17097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21778
          have b5e22757 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op (M.op X0 X3) X2) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e228 X1 (M.op X2 X3) (M.op X0 X3) X2
               have i₂ := b5e13 X0 X3 X2
               grind)
            | exact superpose b5e13 b5e228
            | exact resolve b5e228 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e22879 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X0 X2) (M.op (M.op (M.op X3 X1) X4) X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 X0 X2 (M.op (M.op X3 X1) X4) (M.op X3 X4)
               have i₂ := b5e228 X0 X1 X3 X4
               grind)
            | exact superpose b5e228 b5e34
            | exact resolve b5e34 b5e228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e228
          have b5e23129 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) (M.op X3 X4)) = (M.op (M.op X0 (M.op X3 X1)) X4) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e22879 X0 X1 x X3 X4
               have i₂ := b5e4743 X0 x (M.op X3 X1) X4
               grind)
            | exact superpose b5e4743 b5e22879
            | exact resolve b5e22879 b5e4743
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4743 b5e22879
          have b5e23241 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op (M.op X0 X3) (M.op X2 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e22757 X0 X1 X2 X3
               have i₂ := b5e6061 (M.op X0 X3) X1 X2 X0
               grind)
            | exact superpose b5e6061 b5e22757
            | exact resolve b5e22757 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e22757
          have b5e23665 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) = (M.op X1 (M.op X0 (M.op X3 (M.op X2 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e23241 X0 X1 X2 X3
               have i₂ := b5e6061 X0 X1 X3 (M.op X2 X0)
               grind)
            | exact superpose b5e6061 b5e23241
            | exact resolve b5e23241 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23241
          have b5e29211 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e3117
               have i₂ := b5e707 x
               grind)
            | exact superpose b5e707 b5e3117
            | (have j1 := b5e707 (σ x)
               grind)
            | exact resolve b5e3117 b5e707
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e707 b5e3117
          have b5e29213 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e29211
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29211
            | exact resolve b5e29211 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29211
          have b5e29214 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
          clear b5e29213
          have b5e29231 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e29214
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29214
            | exact resolve b5e29214 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29214
          have b5e32209 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e183 X1 (M.op (M.op X0 X1) X1)
               have i₂ := b5e263 X1 X0
               grind)
            | exact superpose b5e263 b5e183
            | (have j0 := b5e183 X1 X1
               have j1 := b5e263 X1 X1
               grind)
            | exact resolve b5e183 b5e263
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e183 b5e263
          have b5e32275 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X1) X1)) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e32209 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32209
          have b5e32327 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 ∨ (k X1 (M.op X1 X1)) = X1 := by
            intro X1
            first
            | (have i₁ := b5e32275 x X1
               have i₂ := b5e5688 x X1 X1 X1
               grind)
            | (have i₁ := b5e32275 x X1
               have i₂ := b5e5688 x X1 x (M.op (M.op x X1) X1)
               grind)
            | exact superpose b5e5688 b5e32275
            | (have j0 := b5e32275 x X1
               grind)
            | exact resolve b5e32275 b5e5688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32275
          have b5e32480 : ∀ X1 : G, (k X1 (M.op X1 X1)) = X1 := by
            intro X1
            first
            | (have j0 := b5e32327 X1
               have j1 := b5e494 X1
               grind)
            | (have r₁ := b5e32327 x
               have r₂ := b5e494 x
               grind)
            | exact resolve b5e32327 b5e494
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e494 b5e32327
          have b5e32705 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e106 X0 (M.op (σ X0) (σ X0))
               have i₂ := b5e32480 (σ X0)
               grind)
            | exact superpose b5e32480 b5e106
            | exact resolve b5e106 b5e32480
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106 b5e32480
          have b5e32709 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e32705 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e32705
            | exact resolve b5e32705 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32705
          have b5e33677 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x (M.op X0 X1)) x) (M.op y (M.op X2 x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40 (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) X2
               have i₂ := b5e143 X1 X0 X2
               grind)
            | exact superpose b5e143 b5e40
            | exact resolve b5e40 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e33692 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) X3) (M.op X4 X3)) = (M.op (M.op x (M.op X0 X1)) (M.op X4 X2)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e181 (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) X3 X4 X2
               have i₂ := b5e143 X1 X0 X2
               grind)
            | exact superpose b5e143 b5e181
            | exact resolve b5e181 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33710 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x (M.op X0 X1)) X2) y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e4866 X2 (M.op (M.op y (M.op X1 x)) (M.op X2 X0))
               have i₂ := b5e143 X1 X0 X2
               grind)
            | exact superpose b5e143 b5e4866
            | exact resolve b5e4866 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4866
          have b5e33816 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x y) X2) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33710 X0 X1 X2
               have i₂ := b5e9667 x X2 (M.op X0 X1)
               grind)
            | exact superpose b5e9667 b5e33710
            | exact resolve b5e33710 b5e9667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9667 b5e33710
          have b5e33832 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) X3) (M.op X4 X3)) = (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e33692 X0 X1 X2 X3 X4
               have i₂ := b5e23129 x X1 X0 (M.op X4 X2)
               grind)
            | exact superpose b5e23129 b5e33692
            | exact resolve b5e33692 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33692
          have b5e33847 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x x) (M.op X0 X1)) (M.op y (M.op X2 x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33677 X0 X1 X2
               have i₂ := b5e21822 x (M.op X0 X1) (M.op y (M.op X2 x))
               grind)
            | exact superpose b5e21822 b5e33677
            | exact resolve b5e33677 b5e21822
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21822 b5e33677
          have b5e34131 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x X1) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33816 X0 X1 X2
               have i₂ := b5e17097 x X2 X1 X0
               grind)
            | (have i₁ := b5e33816 X0 X1 X2
               have i₂ := b5e17097 x X2 y (M.op X0 X1)
               grind)
            | exact superpose b5e17097 b5e33816
            | exact resolve b5e33816 b5e17097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33816
          have b5e34146 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) y) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e33832 X0 X1 X2 x X4
               have i₂ := b5e5340 (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) x X4
               grind)
            | exact superpose b5e5340 b5e33832
            | exact resolve b5e33832 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33832
          have b5e34161 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x x) X1) (M.op X0 (M.op y (M.op X2 x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e33847 X0 X1 X2
               have i₂ := b5e23129 (M.op x x) X1 X0 (M.op y (M.op X2 x))
               grind)
            | exact superpose b5e23129 b5e33847
            | exact resolve b5e33847 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33847
          have b5e34425 : ∀ X0 X1 X2 : G, (M.op (M.op y x) (M.op (M.op X2 X0) X1)) = (M.op (M.op (M.op x X1) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34131 X0 X1 X2
               have i₂ := b5e7940 (M.op X2 X0) y X1
               grind)
            | exact superpose b5e7940 b5e34131
            | exact resolve b5e34131 b5e7940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34131
          have b5e34440 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) y) (M.op X2 X0)) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34146 X0 X1 X2 X4
               have i₂ := b5e17358 (M.op y (M.op X1 x)) (M.op X2 X0) X4
               grind)
            | exact superpose b5e17358 b5e34146
            | exact resolve b5e34146 b5e17358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34146
          have b5e34455 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x x) X1) (M.op X0 (M.op x (M.op y X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34161 X0 X1 X2
               have i₂ := b5e20500 x X2 X0 y
               grind)
            | (have i₁ := b5e34161 x X1 x
               have i₂ := b5e20500 y x x x
               grind)
            | exact superpose b5e20500 b5e34161
            | exact resolve b5e34161 b5e20500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34161
          have b5e34676 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X1) X2) X0) = (M.op (M.op y x) (M.op X2 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34425 X0 X1 X2
               have i₂ := b5e6061 X2 (M.op y x) X0 X1
               grind)
            | exact superpose b5e6061 b5e34425
            | exact resolve b5e34425 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34425
          have b5e34690 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) y) X0) (M.op X2 X4)) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34440 X0 X1 X2 X4
               have i₂ := b5e23129 (M.op (M.op y (M.op X1 x)) y) X0 X2 X4
               grind)
            | exact superpose b5e23129 b5e34440
            | exact resolve b5e34440 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34440
          have b5e34705 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op (M.op x x) X1) (M.op X0 (M.op x X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34455 X0 X1 X2
               have i₂ := b5e4771 x X2
               grind)
            | exact superpose b5e4771 b5e34455
            | exact resolve b5e34455 b5e4771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34455
          have b5e34891 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) X4) X0) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34690 X0 X1 X2 X4
               have i₂ := b5e17097 (M.op y (M.op X1 x)) X0 X4 X2
               grind)
            | (have i₁ := b5e34690 X2 X1 X2 X4
               have i₂ := b5e17097 (M.op y (M.op X1 x)) X2 y (M.op X2 X4)
               grind)
            | exact superpose b5e17097 b5e34690
            | exact resolve b5e34690 b5e17097
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17097 b5e34690
          have b5e34906 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 x)) (M.op X2 X0)) = (M.op (M.op y X1) (M.op X0 (M.op x X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34705 X0 X1 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e34705
            | exact resolve b5e34705 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34705
          have b5e35049 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op (M.op (M.op y x) (M.op X4 X1)) X0) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e34891 X0 X1 X2 X4
               have i₂ := b5e7940 X4 y X1
               grind)
            | exact superpose b5e7940 b5e34891
            | exact resolve b5e34891 b5e7940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34891
          have b5e35062 : ∀ X0 X1 X2 : G, (M.op (M.op y x) (M.op (M.op X2 X0) X1)) = (M.op (M.op y X1) (M.op X0 (M.op x X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34906 X0 X1 X2
               have i₂ := b5e7940 (M.op X2 X0) y X1
               grind)
            | exact superpose b5e7940 b5e34906
            | exact resolve b5e34906 b5e7940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34906
          have b5e35165 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op x (M.op (M.op X4 X1) X0)) X2) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e35049 X0 X1 X2 X4
               have i₂ := b5e4729 (M.op X4 X1) X0
               grind)
            | exact superpose b5e4729 b5e35049
            | exact resolve b5e35049 b5e4729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4729 b5e35049
          have b5e35174 : ∀ X0 X1 X2 : G, (M.op (M.op y x) (M.op X2 (M.op X0 X1))) = (M.op (M.op y X1) (M.op X0 (M.op x X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35062 X0 X1 X2
               have i₂ := b5e6061 X2 (M.op y x) X0 X1
               grind)
            | exact superpose b5e6061 b5e35062
            | exact resolve b5e35062 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35062
          have b5e35244 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op x X0) (M.op (M.op X4 X1) X2)) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e35165 X0 X1 X2 X4
               have i₂ := b5e23129 x X0 (M.op X4 X1) X2
               grind)
            | exact superpose b5e23129 b5e35165
            | exact resolve b5e35165 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35165
          have b5e35251 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X1) X2) X0) = (M.op (M.op y X1) (M.op X0 (M.op x X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e35174 X0 X1 X2
               have i₂ := b5e34676 X0 X1 X2
               grind)
            | exact superpose b5e34676 b5e35174
            | exact resolve b5e35174 b5e34676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34676 b5e35174
          have b5e35296 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X1) (M.op X0 (M.op X4 X2))) = (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e35244 X0 X1 X2 X4
               have i₂ := b5e6061 X4 (M.op x X0) X1 X2
               grind)
            | exact superpose b5e6061 b5e35244
            | exact resolve b5e35244 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35244
          have b5e35391 : x = (k x (τ (σ x))) ∨ x = y := by
            first
            | (have i₁ := b5e32709 x
               have i₂ := b5e29231
               grind)
            | exact superpose b5e29231 b5e32709
            | exact resolve b5e32709 b5e29231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29231 b5e32709
          have b5e35517 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e35391
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e35391
            | exact resolve b5e35391 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35391
          have b5e35733 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op (M.op X2 (M.op y (M.op X3 x))) X0)) X3) x) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e151 (M.op (M.op y (M.op X1 x)) (M.op (M.op X2 (M.op y (M.op X3 x))) X0)) X3 X2
               have i₂ := b5e143 X1 X0 (M.op X2 (M.op y (M.op X3 x)))
               grind)
            | exact superpose b5e143 b5e151
            | exact resolve b5e151 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35855 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) (M.op y (M.op X1 x)))) = (M.op (M.op (M.op (M.op X0 X1) x) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e182 (M.op X0 (M.op (M.op X2 X3) (M.op y (M.op X1 x)))) X2 X3
               have i₂ := b5e151 X0 X1 (M.op X2 X3)
               grind)
            | exact superpose b5e151 b5e182
            | exact resolve b5e182 b5e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e151
          have b5e35936 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) x) X2) X3) = (M.op X0 (M.op X2 (M.op X3 (M.op y (M.op X1 x))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e35855 X0 X1 X2 X3
               have i₂ := b5e6061 X2 X0 X3 (M.op y (M.op X1 x))
               grind)
            | exact superpose b5e6061 b5e35855
            | exact resolve b5e35855 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35855
          have b5e36041 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) (M.op X2 (M.op y (M.op X3 x)))) x) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e35733 X0 X1 X2 X3
               have i₂ := b5e5824 (M.op X2 (M.op y (M.op X3 x))) (M.op y (M.op X1 x)) X0 X3
               grind)
            | (have i₁ := b5e35733 X3 X1 X2 X0
               have i₂ := b5e5824 X0 (M.op y (M.op X1 x)) (M.op X2 (M.op y (M.op X0 x))) X3
               grind)
            | exact superpose b5e5824 b5e35733
            | exact resolve b5e35733 b5e5824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35733
          have b5e36213 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) x) X2) X3) = (M.op X0 (M.op X2 (M.op X3 (M.op x (M.op y X1))))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e35936 X0 X1 X2 X3
               have i₂ := b5e20500 x X1 X3 y
               grind)
            | (have i₁ := b5e35936 X0 x X2 X3
               have i₂ := b5e20500 y x X3 x
               grind)
            | exact superpose b5e20500 b5e35936
            | exact resolve b5e35936 b5e20500
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20500 b5e35936
          have b5e36309 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) (M.op x X2)) (M.op y (M.op X3 x))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36041 X0 X1 X2 X3
               have i₂ := b5e5824 x (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2 (M.op y (M.op X3 x))
               grind)
            | (have i₁ := b5e36041 X0 X1 X0 X3
               have i₂ := b5e5824 X0 (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) (M.op y (M.op X3 x)) x
               grind)
            | exact superpose b5e5824 b5e36041
            | exact resolve b5e36041 b5e5824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36041
          have b5e36458 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X1) x) X2) X3) = (M.op X0 (M.op X2 (M.op X3 (M.op x X1)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36213 X0 X1 X2 X3
               have i₂ := b5e4771 x X1
               grind)
            | exact superpose b5e4771 b5e36213
            | exact resolve b5e36213 b5e4771
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4771 b5e36213
          have b5e36541 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2) (M.op x (M.op y (M.op X3 x)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36309 X0 X1 X2 X3
               have i₂ := b5e23129 (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2 x (M.op y (M.op X3 x))
               grind)
            | exact superpose b5e23129 b5e36309
            | exact resolve b5e36309 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36309
          have b5e36724 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2) (M.op X3 y)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36541 X0 X1 X2 X3
               have i₂ := b5e23665 x (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2) X3 y
               grind)
            | exact superpose b5e23665 b5e36541
            | exact resolve b5e36541 b5e23665
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23665 b5e36541
          have b5e36856 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e36724 X0 X1 X2 X3
               have i₂ := b5e5387 (M.op (M.op (M.op y (M.op X1 x)) (M.op X0 X3)) X2) X3
               grind)
            | exact superpose b5e5387 b5e36724
            | exact resolve b5e36724 b5e5387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5387 b5e36724
          have b5e36956 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y (M.op X1 x)) y) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36856 X0 X1 X2 x
               have i₂ := b5e17076 (M.op y (M.op X1 x)) X2 X0 x
               grind)
            | exact superpose b5e17076 b5e36856
            | exact resolve b5e36856 b5e17076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17076 b5e36856
          have b5e37035 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op (M.op (M.op (M.op y y) (M.op X1 x)) X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36956 X0 X1 X2
               have i₂ := b5e17358 y (M.op X1 x) X2
               grind)
            | exact superpose b5e17358 b5e36956
            | exact resolve b5e36956 b5e17358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36956
          have b5e37085 : ∀ X0 X1 X2 : G, (M.op (M.op x (M.op X0 X1)) X2) = (M.op y (M.op X2 (M.op X0 (M.op X1 x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37035 X0 X1 X2
               have i₂ := b5e16794 y (M.op X1 x) X2 X0
               grind)
            | exact superpose b5e16794 b5e37035
            | exact resolve b5e37035 b5e16794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e16794 b5e37035
          have b5e37114 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) (M.op X0 X2)) = (M.op y (M.op X2 (M.op X0 (M.op X1 x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e37085 X0 X1 X2
               have i₂ := b5e23129 x X1 X0 X2
               grind)
            | exact superpose b5e23129 b5e37085
            | exact resolve b5e37085 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37085
          have b5e37469 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op (M.op x (M.op X0 X1)) (M.op y (M.op X3 x))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e164 (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2 X3
               have i₂ := b5e143 X1 X0 x
               grind)
            | exact superpose b5e143 b5e164
            | exact resolve b5e164 b5e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e143 b5e164
          have b5e37977 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op (M.op x y) (M.op X3 (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e37469 X0 X1 X2 X3
               have i₂ := b5e35296 y (M.op X0 X1) x X3
               grind)
            | (have i₁ := b5e37469 X0 X1 X2 X1
               have i₂ := b5e35296 (M.op X0 X1) X1 x y
               grind)
            | exact superpose b5e35296 b5e37469
            | exact resolve b5e37469 b5e35296
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35296 b5e37469
          have b5e38433 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op y (M.op (M.op X3 (M.op (M.op X0 X1) x)) x)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e37977 X0 X1 X2 X3
               have i₂ := b5e5335 (M.op X3 (M.op (M.op X0 X1) x))
               grind)
            | exact superpose b5e5335 b5e37977
            | exact resolve b5e37977 b5e5335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5335 b5e37977
          have b5e38853 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op y (M.op x (M.op X3 (M.op (M.op X0 X1) x)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e38433 X0 X1 X2 X3
               have i₂ := b5e11691 x (M.op X3 (M.op (M.op X0 X1) x))
               grind)
            | (have i₁ := b5e38433 X0 X1 X2 X3
               have i₂ := b5e11691 (M.op X3 (M.op (M.op X0 X1) x)) x
               grind)
            | exact superpose b5e11691 b5e38433
            | exact resolve b5e38433 b5e11691
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e11691 b5e38433
          have b5e39200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op (M.op x (M.op X0 X1)) (M.op X3 x)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e38853 X0 X1 X2 X3
               have i₂ := b5e37114 X3 (M.op X0 X1) x
               grind)
            | exact superpose b5e37114 b5e38853
            | exact resolve b5e38853 b5e37114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37114 b5e38853
          have b5e39436 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) X2) (M.op X3 X2)) = (M.op (M.op x X1) (M.op X0 (M.op X3 x))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e39200 X0 X1 X2 X3
               have i₂ := b5e23129 x X1 X0 (M.op X3 x)
               grind)
            | exact superpose b5e23129 b5e39200
            | exact resolve b5e39200 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39200
          have b5e39614 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) (M.op x X0)) y) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39436 X0 X1 x X3
               have i₂ := b5e5340 (M.op (M.op y (M.op X1 x)) (M.op x X0)) x X3
               grind)
            | exact superpose b5e5340 b5e39436
            | exact resolve b5e39436 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39436
          have b5e39747 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) y) (M.op x X0)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39614 X0 X1 X3
               have i₂ := b5e17358 (M.op y (M.op X1 x)) (M.op x X0) X3
               grind)
            | exact superpose b5e17358 b5e39614
            | exact resolve b5e39614 b5e17358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17358 b5e39614
          have b5e39824 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) y) X0) (M.op x X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39747 X0 X1 X3
               have i₂ := b5e23129 (M.op (M.op y (M.op X1 x)) y) X0 x X3
               grind)
            | exact superpose b5e23129 b5e39747
            | exact resolve b5e39747 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39747
          have b5e39875 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op (M.op (M.op (M.op y (M.op X1 x)) x) X3) X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39824 X0 X1 X3
               have i₂ := b5e10632 (M.op y (M.op X1 x)) X0 X3
               grind)
            | exact superpose b5e10632 b5e39824
            | exact resolve b5e39824 b5e10632
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e10632 b5e39824
          have b5e39908 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op y (M.op X3 (M.op X0 (M.op x (M.op X1 x))))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39875 X0 X1 X3
               have i₂ := b5e36458 y (M.op X1 x) X3 X0
               grind)
            | exact superpose b5e36458 b5e39875
            | exact resolve b5e39875 b5e36458
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36458 b5e39875
          have b5e39925 : ∀ X0 X1 X3 : G, (M.op (M.op x X1) (M.op X0 (M.op X3 x))) = (M.op y (M.op X3 (M.op X0 X1))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b5e39908 X0 X1 X3
               have i₂ := b5e4777 X0 x X1
               grind)
            | exact superpose b5e4777 b5e39908
            | exact resolve b5e39908 b5e4777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4777 b5e39908
          have b5e39970 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e70 x x
               have i₂ := b5e35517
               grind)
            | exact superpose b5e35517 b5e70
            | (have j0 := b5e70 x x
               grind)
            | exact resolve b5e70 b5e35517
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e35517
          have b5e39971 : x = (M.op x x) ∨ x = y := by grind
          clear b5e39970
          have b5e39995 : x = y ∨ x = y := by
            first
            | (have i₁ := b5e39971
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e39971
            | exact resolve b5e39971 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39971
          have b5e39996 : x = y := by grind
          clear b5e39995
          have b5e40414 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op (M.op X0 X1) x)) X2) = (M.op (M.op (M.op x X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e182 (M.op (M.op y (M.op (M.op X0 X1) x)) X2) X1 X2
               have i₂ := b5e174 X0 X1 X2
               grind)
            | exact superpose b5e174 b5e182
            | exact resolve b5e182 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e182
          have b5e40441 : ∀ X0 X1 X2 : G, x = (M.op (M.op y (M.op (M.op y (M.op (M.op X0 X1) x)) X2)) (M.op (M.op x X0) (M.op x (M.op X1 X2)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e38 (M.op (M.op y (M.op (M.op X0 X1) x)) X2) (M.op X1 X2)
               have i₂ := b5e174 X0 X1 X2
               grind)
            | exact superpose b5e174 b5e38
            | exact resolve b5e38 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e40460 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op (M.op (M.op (M.op y (M.op (M.op X0 X1) x)) X2) X3) (M.op X4 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e181 (M.op (M.op y (M.op (M.op X0 X1) x)) X2) X3 X4 (M.op X1 X2)
               have i₂ := b5e174 X0 X1 X2
               grind)
            | exact superpose b5e174 b5e181
            | exact resolve b5e181 b5e174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e174 b5e181
          have b5e40505 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op (M.op (M.op (M.op y (M.op (M.op X0 X1) x)) X2) y) X4) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e40460 X0 X1 X2 x X4
               have i₂ := b5e5340 (M.op (M.op y (M.op (M.op X0 X1) x)) X2) x X4
               grind)
            | exact superpose b5e5340 b5e40460
            | exact resolve b5e40460 b5e5340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5340 b5e40460
          have b5e40524 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x (M.op (M.op y (M.op (M.op X0 X1) x)) X2)) (M.op X1 X2)) (M.op x X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40441 X0 X1 X2
               have i₂ := b5e35251 (M.op x X0) (M.op (M.op y (M.op (M.op X0 X1) x)) X2) (M.op X1 X2)
               grind)
            | exact superpose b5e35251 b5e40441
            | exact resolve b5e40441 b5e35251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35251 b5e40441
          have b5e40551 : ∀ X0 X1 X2 : G, (M.op (M.op y x) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op x X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40414 X0 X1 X2
               have i₂ := b5e7940 X2 y (M.op X0 X1)
               grind)
            | exact superpose b5e7940 b5e40414
            | exact resolve b5e40414 b5e7940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7940 b5e40414
          have b5e40901 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op y (M.op X4 (M.op (M.op (M.op X0 X1) x) X2))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e40505 X0 X1 X2 X4
               have i₂ := b5e5690 y (M.op (M.op X0 X1) x) X2 X4
               grind)
            | exact superpose b5e5690 b5e40505
            | exact resolve b5e40505 b5e5690
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5690 b5e40505
          have b5e40920 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x (M.op (M.op y (M.op (M.op X0 X1) x)) X2)) X2) (M.op X1 (M.op x X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40524 X0 X1 X2
               have i₂ := b5e23129 (M.op x (M.op (M.op y (M.op (M.op X0 X1) x)) X2)) X2 X1 (M.op x X0)
               grind)
            | exact superpose b5e23129 b5e40524
            | exact resolve b5e40524 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40524
          have b5e40944 : ∀ X0 X1 X2 : G, (M.op (M.op x x) (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op x X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40551 X0 X1 X2
               have i₂ := b5e39996
               grind)
            | exact superpose b5e39996 b5e40551
            | exact resolve b5e40551 b5e39996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40551
          have b5e41269 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op y (M.op X4 (M.op (M.op X0 X1) (M.op x X2)))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e40901 X0 X1 X2 X4
               have i₂ := b5e6061 (M.op X0 X1) X4 x X2
               grind)
            | exact superpose b5e6061 b5e40901
            | exact resolve b5e40901 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40901
          have b5e41286 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x X2) (M.op (M.op y (M.op (M.op X0 X1) x)) X2)) (M.op X1 (M.op x X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40920 X0 X1 X2
               have i₂ := b5e23129 x X2 (M.op y (M.op (M.op X0 X1) x)) X2
               grind)
            | exact superpose b5e23129 b5e40920
            | exact resolve b5e40920 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40920
          have b5e41309 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) X1) X2) = (M.op y (M.op X2 (M.op X0 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e40944 X0 X1 X2
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e40944
            | exact resolve b5e40944 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40944
          have b5e41620 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op y (M.op X4 (M.op X0 (M.op X1 (M.op x X2))))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e41269 X0 X1 X2 X4
               have i₂ := b5e6061 X0 X4 X1 (M.op x X2)
               grind)
            | exact superpose b5e6061 b5e41269
            | exact resolve b5e41269 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41269
          have b5e41637 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x X2) (M.op X2 (M.op X1 (M.op x X0)))) (M.op y (M.op (M.op X0 X1) x))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41286 X0 X1 X2
               have i₂ := b5e5824 (M.op y (M.op (M.op X0 X1) x)) (M.op x X2) X2 (M.op X1 (M.op x X0))
               grind)
            | (have i₁ := b5e41286 X0 X1 x
               have i₂ := b5e5824 (M.op X1 (M.op x X0)) (M.op x x) (M.op y (M.op (M.op X0 X1) x)) x
               grind)
            | exact superpose b5e5824 b5e41286
            | exact resolve b5e41286 b5e5824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41286
          have b5e41660 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 (M.op X0 X1))) = (M.op (M.op (M.op x X0) X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41309 X0 X1 X2
               have i₂ := b5e39996
               grind)
            | exact superpose b5e39996 b5e41309
            | exact resolve b5e41309 b5e39996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41309
          have b5e41948 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x X0) (M.op X4 (M.op X1 X2))) = (M.op x (M.op X4 (M.op X0 (M.op X1 (M.op x X2))))) := by
            intro X0 X1 X2 X4
            first
            | (have i₁ := b5e41620 X0 X1 X2 X4
               have i₂ := b5e39996
               grind)
            | exact superpose b5e39996 b5e41620
            | exact resolve b5e41620 b5e39996
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39996 b5e41620
          have b5e41965 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op x X2) (M.op X1 (M.op x X0))) (M.op X2 (M.op y (M.op (M.op X0 X1) x)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41637 X0 X1 X2
               have i₂ := b5e23129 (M.op x X2) (M.op X1 (M.op x X0)) X2 (M.op y (M.op (M.op X0 X1) x))
               grind)
            | exact superpose b5e23129 b5e41637
            | exact resolve b5e41637 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41637
          have b5e42251 : ∀ X0 X1 X2 : G, x = (M.op x (M.op (M.op X2 (M.op y (M.op (M.op X0 X1) x))) (M.op X2 (M.op X1 (M.op x X0))))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41965 X0 X1 X2
               have i₂ := b5e41660 X2 (M.op X1 (M.op x X0)) (M.op X2 (M.op y (M.op (M.op X0 X1) x)))
               grind)
            | exact superpose b5e41660 b5e41965
            | exact resolve b5e41965 b5e41660
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41660 b5e41965
          have b5e42464 : ∀ X0 X1 X2 : G, x = (M.op (M.op x X2) (M.op (M.op X2 (M.op y (M.op (M.op X0 X1) x))) (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42251 X0 X1 X2
               have i₂ := b5e41948 X2 X1 X0 (M.op X2 (M.op y (M.op (M.op X0 X1) x)))
               grind)
            | exact superpose b5e41948 b5e42251
            | exact resolve b5e42251 b5e41948
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41948 b5e42251
          have b5e42608 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op y (M.op (M.op X0 X1) x))) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42464 X0 X1 x
               have i₂ := b5e5688 x x (M.op y (M.op (M.op X0 X1) x)) (M.op X1 X0)
               grind)
            | (have i₁ := b5e42464 X0 X1 x
               have i₂ := b5e5688 X0 x x (M.op (M.op x (M.op y (M.op (M.op X0 X1) x))) (M.op X1 X0))
               grind)
            | exact superpose b5e5688 b5e42464
            | exact resolve b5e42464 b5e5688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5688 b5e42464
          have b5e42718 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op (M.op X1 X0) y)) (M.op (M.op X0 X1) x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42608 X0 X1
               have i₂ := b5e5824 (M.op X1 X0) x y (M.op (M.op X0 X1) x)
               grind)
            | (have i₁ := b5e42608 X0 X1
               have i₂ := b5e5824 y x (M.op (M.op X0 X1) x) (M.op X1 X0)
               grind)
            | exact superpose b5e5824 b5e42608
            | exact resolve b5e42608 b5e5824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5824 b5e42608
          have b5e42792 : ∀ X0 X1 : G, x = (M.op (M.op x y) (M.op (M.op X1 X0) (M.op (M.op X0 X1) x))) := by
            intro X0 X1
            first
            | (have i₁ := b5e42718 X0 X1
               have i₂ := b5e23129 x y (M.op X1 X0) (M.op (M.op X0 X1) x)
               grind)
            | exact superpose b5e23129 b5e42718
            | exact resolve b5e42718 b5e23129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e23129 b5e42718
          have b5e42850 : ∀ X0 X1 : G, x = (M.op y (M.op (M.op X0 X1) (M.op (M.op X1 X0) y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e42792 X0 X1
               have i₂ := b5e39925 (M.op X1 X0) y (M.op X0 X1)
               grind)
            | exact superpose b5e39925 b5e42792
            | exact resolve b5e42792 b5e39925
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39925 b5e42792
          have b5e42882 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 (M.op (M.op X1 X0) y)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e42850 X0 X1
               have i₂ := b5e6061 X0 y X1 (M.op (M.op X1 X0) y)
               grind)
            | exact superpose b5e6061 b5e42850
            | exact resolve b5e42850 b5e6061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6061 b5e42850
          have b5e42905 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op X1 (M.op y (M.op X1 X0))))) := by
            intro X0 X1
            first
            | (have i₁ := b5e42882 X0 X1
               have i₂ := b5e6475 X1 y X0 (M.op X1 X0)
               grind)
            | (have i₁ := b5e42882 X0 X1
               have i₂ := b5e6475 X1 (M.op X1 X0) X0 y
               grind)
            | exact superpose b5e6475 b5e42882
            | exact resolve b5e42882 b5e6475
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6475 b5e42882
          have b5e42922 : ∀ X0 : G, x = (M.op y (M.op X0 (M.op X0 y))) := by
            intro X0
            first
            | (have i₁ := b5e42905 X0 x
               have i₂ := b5e17082 X0 x y y X0
               grind)
            | exact superpose b5e17082 b5e42905
            | exact resolve b5e42905 b5e17082
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e17082 b5e42905
          have b5e42932 : x = (M.op y y) := by
            first
            | (have i₁ := b5e42922 x
               have i₂ := b5e15523 y x
               grind)
            | exact superpose b5e15523 b5e42922
            | exact resolve b5e42922 b5e15523
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e15523 b5e42922
          have b5e42940 : False := by grind
          exact b5e42940
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y y) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 X1 (τ X0)
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
             have i₂ := b6e12 X0 X3 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k X0 (τ X1))
             have i₂ := b6e26 X1 X0
             grind)
          | exact superpose b6e26 b6e13
          | exact resolve b6e13 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e50 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e73 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          grind
        have b6e78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
        have b6e200 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X2) = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 x X2
             have i₂ := b6e28 X0 x X2 X1
             grind)
          | exact superpose b6e28 b6e12
          | exact resolve b6e12 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e333 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
             have i₂ := b6e30 (M.op X1 X2) X0 X1 X2
             grind)
          | exact superpose b6e30 b6e12
          | exact resolve b6e12 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e540 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X2 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e333 X1 (M.op X0 (M.op X2 X2)) X2
             have i₂ := b6e200 X0 X2 X2
             grind)
          | exact superpose b6e200 b6e333
          | exact resolve b6e333 b6e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e200 b6e333
        have b6e1105 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e50 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e1789 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b6e540 X1 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e540
          | exact resolve b6e540 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e540
        have b6e2170 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by grind
        clear b6e1789
        have b6e2192 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
          first
          | (have j1 := b6e1105 (σ x)
             grind)
          | (have r₁ := b6e2170
             have r₂ := b6e1105 (σ x)
             grind)
          | exact resolve b6e2170 b6e1105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2170
        have b6e8103 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e78 y y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e78
          | exact resolve b6e78 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e78
        have b6e8437 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by grind
        clear b6e8103
        have b6e15064 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e8437
             grind)
          | exact superpose b6e8437 b6e13
          | exact resolve b6e13 b6e8437
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e15078 : x = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e15064
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e15064
          | exact resolve b6e15064 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15064
        have b6e15100 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e73 y y
             have i₂ := b6e15078
             grind)
          | exact superpose b6e15078 b6e73
          | (have j0 := b6e73 y x
             grind)
          | exact resolve b6e73 b6e15078
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15078
        have b6e15104 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
        clear b6e15100
        have b6e15113 : y = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e15104
             have r₂ := b6e20
             grind)
          | exact resolve b6e15104 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15104
        have b6e16214 : (τ (σ x)) = (k x (τ (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b6e43 x (M.op (σ x) (σ x))
             have i₂ := b6e2192
             grind)
          | exact superpose b6e2192 b6e43
          | exact resolve b6e43 b6e2192
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2192
        have b6e16216 : x = (k x (τ (M.op (σ x) (σ x)))) := by
          first
          | (have i₁ := b6e16214
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e16214
          | exact resolve b6e16214 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16214
        have b6e17009 : y ≠ (M.op y y) ∨ y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1105 y
             have i₂ := b6e15113
             grind)
          | exact superpose b6e15113 b6e1105
          | exact resolve b6e1105 b6e15113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1105
        have b6e17044 : y = (k y y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e17009
             have r₂ := b6e15113
             grind)
          | exact resolve b6e17009 b6e15113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e15113 b6e17009
        have b6e17123 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e8437
             have i₂ := b6e17044
             grind)
          | exact superpose b6e17044 b6e8437
          | exact resolve b6e8437 b6e17044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8437 b6e17044
        have b6e17148 : (σ x) = (σ y) := by grind
        clear b6e17123
        have b6e17255 : x = (k x (τ (M.op (σ y) (σ y)))) := by
          first
          | (have i₁ := b6e16216
             have i₂ := b6e17148
             grind)
          | exact superpose b6e17148 b6e16216
          | exact resolve b6e16216 b6e17148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e16216
        have b6e17256 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e17148
             grind)
          | exact superpose b6e17148 b6e13
          | exact resolve b6e13 b6e17148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e17260 : ∀ X0 : G, (τ (k (σ y) X0)) = (k x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e43 x X0
             have i₂ := b6e17148
             grind)
          | exact superpose b6e17148 b6e43
          | exact resolve b6e43 b6e17148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17148
        have b6e17269 : ∀ X0 : G, (k y (τ X0)) = (k x (τ X0)) := by
          intro X0
          first
          | (have i₁ := b6e17260 X0
             have i₂ := b6e43 y X0
             grind)
          | exact superpose b6e43 b6e17260
          | exact resolve b6e17260 b6e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e17260
        have b6e17273 : x = y := by
          first
          | (have i₁ := b6e17256
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e17256
          | exact resolve b6e17256 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17256
        have b6e17274 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b6e17255
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e17255
          | exact resolve b6e17255 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17255
        have b6e17291 : x = (k y (τ (σ x))) := by
          first
          | (have i₁ := b6e17274
             have i₂ := b6e17269 (σ x)
             grind)
          | exact superpose b6e17269 b6e17274
          | exact resolve b6e17274 b6e17269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17269 b6e17274
        have b6e17306 : x = (k y x) := by
          first
          | (have i₁ := b6e17291
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e17291
          | exact resolve b6e17291 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17291
        have b6e17313 : y = (k y y) := by
          first
          | (have i₁ := b6e17306
             have i₂ := b6e17273
             grind)
          | exact superpose b6e17273 b6e17306
          | exact resolve b6e17306 b6e17273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17306
        have b6e17412 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e17273
             grind)
          | exact superpose b6e17273 b6e21
          | exact resolve b6e21 b6e17273
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e17273
        have b6e17594 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e73 y y
             have i₂ := b6e17313
             grind)
          | exact superpose b6e17313 b6e73
          | (have j0 := b6e73 y y
             grind)
          | exact resolve b6e73 b6e17313
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73 b6e17313
        have b6e17595 : y = (M.op y y) := by grind
        clear b6e17594
        have b6e17618 : False := by grind
        exact b6e17618
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X0 (M.op X3 X2)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op (M.op X0 X1) (M.op X2 X1)) X2 X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X0 X3) (M.op X2 X3))) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 X2 (M.op (M.op X0 X3) (M.op X2 X3))
               have i₂ := b7e13 X0 X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e55 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            grind
          have b7e56 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e51
               have r₂ := b7e23
               grind)
            | exact resolve b7e51 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e57 : (σ x) = (σ (k x y)) := by
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
          have b7e60 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e14
            | exact resolve b7e14 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e61 : x = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e84 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            grind
          have b7e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
          have b7e98 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e99 : x = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e98
               have r₂ := b7e21
               grind)
            | exact resolve b7e98 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e101 : x = (M.op x y) := by
            first
            | (have r₁ := b7e99
               have r₂ := b7e22
               grind)
            | exact resolve b7e99 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op y X1)) = (M.op (M.op X0 x) x) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 X0 X1 y x
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e34
            | exact resolve b7e34 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e225 : ∀ X0 X1 : G, x = (M.op (M.op x X0) (M.op (M.op X0 X1) (M.op y X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X0 x y X1
               have i₂ := b7e101
               grind)
            | exact superpose b7e101 b7e36
            | exact resolve b7e36 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e268 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op X1 X2) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 (M.op X0 X1) (M.op X1 X2) (M.op (M.op X1 X2) X2)
               have i₂ := b7e36 (M.op X1 X2) X0 X1 X2
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e298 : ∀ X0 : G, x = (M.op (M.op x X0) (M.op (M.op X0 x) x)) := by
            intro X0
            first
            | (have i₁ := b7e225 X0 x
               have i₂ := b7e177 X0 x
               grind)
            | exact superpose b7e177 b7e225
            | exact resolve b7e225 b7e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e177 b7e225
          have b7e306 : ∀ X0 : G, x = (M.op (M.op x X0) X0) := by
            intro X0
            first
            | (have i₁ := b7e298 X0
               have i₂ := b7e268 (M.op x X0) X0 x
               grind)
            | exact superpose b7e268 b7e298
            | exact resolve b7e298 b7e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e268 b7e298
          have b7e497 : ∀ X0 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b7e55 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e2726 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e90 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e90
            | exact resolve b7e90 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e3006 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
          clear b7e2726
          have b7e6941 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e3006
               grind)
            | exact superpose b7e3006 b7e14
            | exact resolve b7e14 b7e3006
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e6959 : y = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e6941
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e6941
            | exact resolve b7e6941 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6941
          have b7e9713 : x ≠ x ∨ x = (k x (M.op x x)) := by
            first
            | (have i₁ := b7e497 x
               have i₂ := b7e306 x
               grind)
            | exact superpose b7e306 b7e497
            | (have j0 := b7e497 x
               grind)
            | (have r₁ := b7e497 x
               have r₂ := b7e306 x
               grind)
            | exact resolve b7e497 b7e306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e306 b7e497
          have b7e9724 : x = (k x (M.op x x)) := by grind
          clear b7e9713
          have b7e9822 : y = (M.op x x) ∨ y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e84 x x
               have i₂ := b7e6959
               grind)
            | exact superpose b7e6959 b7e84
            | (have j0 := b7e84 x y
               grind)
            | exact resolve b7e84 b7e6959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e84 b7e6959
          have b7e9826 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
          clear b7e9822
          have b7e9835 : x = (M.op x x) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b7e9826
               have r₂ := b7e22
               grind)
            | exact resolve b7e9826 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9826
          have b7e9957 : x = (k x x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e9724
               have i₂ := b7e9835
               grind)
            | exact superpose b7e9835 b7e9724
            | exact resolve b7e9724 b7e9835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e9724 b7e9835
          have b7e10394 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3006
               have i₂ := b7e9957
               grind)
            | exact superpose b7e9957 b7e3006
            | exact resolve b7e3006 b7e9957
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3006 b7e9957
          have b7e10419 : (σ x) = (σ y) := by grind
          clear b7e10394
          have b7e10810 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e10419
               grind)
            | exact superpose b7e10419 b7e23
            | exact resolve b7e23 b7e10419
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e10865 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b7e10810
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e10810
            | exact resolve b7e10810 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10810
          have b7e10878 : False := by grind
          exact b7e10878
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e82 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (σ y)
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 (σ y)
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
          have b8e929 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e82 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82
          have b8e930 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e929
               have r₂ := b8e24
               grind)
            | exact resolve b8e929 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e929
          have b8e931 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e930
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e930
            | exact resolve b8e930 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e930
          have b8e932 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e931
               grind)
            | exact superpose b8e931 b8e20
            | exact resolve b8e20 b8e931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e931
          have b8e957 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e932
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e932
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e932 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e932
          have b8e958 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e957
          have b8e960 : y = (M.op x x) := by
            first
            | (have r₁ := b8e958
               have r₂ := b8e21
               grind)
            | exact resolve b8e958 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e958
          have b8e963 : False := by grind
          exact b8e963

/-- `Equation2702`: `x = ((y ◇ x) ◇ (x ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_pyx_pxy_Equation2702 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2702 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2702.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e37 : (M.op x y) = (k x y) := by grind
      have b0e38 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e40 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e38
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e38
        | exact resolve b0e38 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e41 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e40
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e40
        | exact resolve b0e40 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e40
      have b0e42 : False := by grind
      exact b0e42
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b1e29 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
          intro X0 X3
          first
          | (have i₁ := b1e12 X0 (M.op (M.op x X0) (M.op X0 x)) X3
             have i₂ := b1e12 X0 x x
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (M.op x y) = (k x y) := by grind
        have b1e38 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
        have b1e43 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e38
        have b1e44 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e43
             have r₂ := b1e21
             grind)
          | exact resolve b1e43 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e45 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e44
          | exact resolve b1e44 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e46 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e45
             have i₂ := b1e36
             grind)
          | exact superpose b1e36 b1e45
          | exact resolve b1e45 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e45
        have b1e66 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
          first
          | (have i₁ := b1e29 (σ x) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e29
          | exact resolve b1e29 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e67 : x = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b1e29 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e72 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e66
          | exact resolve b1e66 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e129 : (σ (M.op x y)) = (σ x) := by
          first
          | (have i₁ := b1e72
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e72
          | exact resolve b1e72 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e72
        have b1e137 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e129
             grind)
          | exact superpose b1e129 b1e24
          | exact resolve b1e24 b1e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e140 : (M.op x y) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x y)
             have i₂ := b1e129
             grind)
          | exact superpose b1e129 b1e13
          | exact resolve b1e13 b1e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e129
        have b1e141 : x = (M.op x y) := by
          first
          | (have i₁ := b1e140
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e140
          | exact resolve b1e140 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e140
        have b1e165 : x = (M.op x x) := by
          first
          | (have i₁ := b1e67
             have i₂ := b1e141
             grind)
          | exact superpose b1e141 b1e67
          | exact resolve b1e67 b1e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e67 b1e141
        have b1e175 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e165
             grind)
          | exact superpose b1e165 b1e20
          | exact resolve b1e20 b1e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e165
        have b1e202 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e137
             have i₂ := b1e175
             grind)
          | exact superpose b1e175 b1e137
          | exact resolve b1e137 b1e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e137 b1e175
        have b1e204 : False := by grind
        exact b1e204
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e33 : (M.op x y) = (k x y) := by grind
        have b2e45 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e182 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e45 x y
             grind)
          | exact superpose b2e45 b2e19
          | (have j1 := b2e45 x y
             grind)
          | exact resolve b2e19 b2e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e219 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e182
             have r₂ := b2e21
             grind)
          | exact resolve b2e182 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e224 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e219
             have r₂ := b2e22
             grind)
          | exact resolve b2e219 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e219
        have b2e225 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b2e224
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e224
          | exact resolve b2e224 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e224
        have b2e226 : False := by grind
        exact b2e226
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
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
        have b3e29 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
          intro X0 X3
          first
          | (have i₁ := b3e12 X0 (M.op (M.op x X0) (M.op X0 x)) X3
             have i₂ := b3e12 X0 x x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : x = (M.op (M.op x y) x) := by
          first
          | (have i₁ := b3e29 x y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e29
          | exact resolve b3e29 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : x = (M.op y x) := by
          first
          | (have i₁ := b3e33
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e33
          | exact resolve b3e33 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e42 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e43 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e42
          | exact resolve b3e42 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e51 : y ≠ y ∨ y = (M.op x x) ∨ (M.op y x) = (k x y) := by
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
        have b3e54 : y = (M.op x x) ∨ (M.op y x) = (k x y) := by grind
        clear b3e51
        have b3e58 : (M.op y x) = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e20
             grind)
          | exact resolve b3e54 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e61 : x = (k x y) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e41
             grind)
          | exact superpose b3e41 b3e58
          | exact resolve b3e58 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41 b3e58
        have b3e123 : (σ x) = (M.op (M.op (σ x) (σ (k x y))) (σ x)) := by
          first
          | (have i₁ := b3e29 (σ x) (σ y)
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e29
          | exact resolve b3e29 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e128 : (σ x) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
          first
          | (have i₁ := b3e123
             have i₂ := b3e61
             grind)
          | exact superpose b3e61 b3e123
          | exact resolve b3e123 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e123
        have b3e130 : (σ x) = (M.op (σ y) (σ x)) := by
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
        have b3e149 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
          first
          | (have i₁ := b3e29 (σ y) (σ x)
             have i₂ := b3e130
             grind)
          | exact superpose b3e130 b3e29
          | exact resolve b3e29 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e153 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e149
             have i₂ := b3e130
             grind)
          | exact superpose b3e130 b3e149
          | exact resolve b3e149 b3e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130 b3e149
        have b3e155 : False := by grind
        exact b3e155
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b5e30 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
            intro X0 X3
            first
            | (have i₁ := b5e13 X0 (M.op (M.op x X0) (M.op X0 x)) X3
               have i₂ := b5e13 X0 x x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, x = (M.op (M.op (M.op X0 x) y) x) := by
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
          have b5e33 : x = (M.op (M.op x y) x) := by
            first
            | (have i₁ := b5e30 x y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e30
            | exact resolve b5e30 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (M.op X0 (M.op X0 X1)) X0) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e30 (M.op X0 (M.op X0 X1)) X0
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e30
            | exact resolve b5e30 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X0 X1
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e35
            | exact resolve b5e35 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e40 : x = (M.op y x) := by
            first
            | (have i₁ := b5e33
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e42 : ∀ X0 : G, y = (M.op (M.op (M.op X0 y) x) y) := by
            intro X0
            first
            | (have i₁ := b5e13 y X0 x
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e13
            | exact resolve b5e13 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : y ≠ y ∨ y = (M.op x x) ∨ (M.op y x) = (k x y) := by
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
          have b5e47 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 (M.op X0 (M.op X0 X1))) = (k (M.op X0 (M.op X0 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (M.op X0 (M.op X0 X1)) X0
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e17
            | (have j0 := b5e17 (M.op X0 (M.op X0 X1)) X0
               grind)
            | (have r₁ := b5e17 (M.op X0 (M.op X0 x)) X0
               have r₂ := b5e30 X0 x
               grind)
            | exact resolve b5e17 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 (M.op X0 (M.op X0 X1))) = (k (M.op X0 (M.op X0 X1)) X0) := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e52 : y = (M.op x x) ∨ (M.op y x) = (k x y) := by grind
          clear b5e45
          have b5e54 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1))) = X0 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e50 X0 X1
               have i₂ := b5e38 X0 X1
               grind)
            | exact superpose b5e38 b5e50
            | (have j0 := b5e50 X0 X1
               grind)
            | exact resolve b5e50 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e50
          have b5e56 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b5e52
               have r₂ := b5e21
               grind)
            | exact resolve b5e52 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e57 : x = (k x y) := by
            first
            | (have i₁ := b5e56
               have i₂ := b5e40
               grind)
            | exact superpose b5e40 b5e56
            | exact resolve b5e56 b5e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40 b5e56
          have b5e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e67 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e129 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e70 (σ X1) (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | (have j1 := b5e70 (σ X1) (σ X0)
               grind)
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e199 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e61 X0 X1
               grind)
            | exact superpose b5e61 b5e13
            | (have j1 := b5e61 X0 X1
               grind)
            | exact resolve b5e13 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e200 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X1) (σ X0) X2
               have i₂ := b5e61 X0 X1
               grind)
            | exact superpose b5e61 b5e13
            | (have j1 := b5e61 X0 X1
               grind)
            | exact resolve b5e13 b5e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e996 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1663 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (k (M.op X0 (M.op X0 X1)) X0) ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) := by
            intro X0 X1
            grind
          clear b5e54
          have b5e1682 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) ∨ (k (M.op X0 (M.op X0 X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1663 X0 X1
               have i₂ := b5e30 X0 X1
               grind)
            | exact superpose b5e30 b5e1663
            | (have j0 := b5e1663 X0 X1
               grind)
            | exact resolve b5e1663 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1663
          have b5e2266 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e199 x y X0
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e199
            | (have j0 := b5e199 x y x
               grind)
            | exact resolve b5e199 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e199
          have b5e2305 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2266 X0
               grind)
            | (have r₁ := b5e2266 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2266 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2266
          have b5e2309 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ x)) := by
            intro X0
            first
            | (have j0 := b5e2305 X0
               grind)
            | (have r₁ := b5e2305 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2305 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2305
          have b5e2328 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e2309 (M.op x (σ x))
               have i₂ := b5e2309 x
               grind)
            | exact superpose b5e2309 b5e2309
            | exact resolve b5e2309 b5e2309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2309
          have b5e2369 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e200 x y X0
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e200
            | (have j0 := b5e200 x y x
               grind)
            | exact resolve b5e200 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e200
          have b5e2527 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2369 X0
               grind)
            | (have r₁ := b5e2369 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e2369 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2369
          have b5e2531 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op (σ y) X0)) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e2527 X0
               grind)
            | (have r₁ := b5e2527 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e2527 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2527
          have b5e5589 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ (k y X0))) (σ y)) ∨ (σ X0) = (M.op (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e2531 (σ X0)
               have i₂ := b5e129 y X0
               grind)
            | exact superpose b5e129 b5e2531
            | (have j1 := b5e129 y X0
               grind)
            | exact resolve b5e2531 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e18741 : ∀ X0 : G, (M.op (M.op (M.op X0 y) x) y) = (k (M.op (M.op (M.op X0 y) x) y) (M.op (M.op X0 y) x)) ∨ (M.op (M.op X0 y) x) = (k (M.op (M.op (M.op X0 y) x) y) (M.op (M.op X0 y) x)) := by
            intro X0
            first
            | (have i₁ := b5e1682 (M.op (M.op X0 y) x) y
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e1682
            | exact resolve b5e1682 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1682
          have b5e18866 : ∀ X0 : G, y = (k y (M.op (M.op X0 y) x)) ∨ (M.op (M.op X0 y) x) = (k (M.op (M.op (M.op X0 y) x) y) (M.op (M.op X0 y) x)) := by
            intro X0
            first
            | (have i₁ := b5e18741 X0
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e18741
            | (have j0 := b5e18741 X0
               grind)
            | exact resolve b5e18741 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18741
          have b5e18911 : ∀ X0 : G, (M.op (M.op X0 y) x) = (k y (M.op (M.op X0 y) x)) ∨ y = (k y (M.op (M.op X0 y) x)) := by
            intro X0
            first
            | (have i₁ := b5e18866 X0
               have i₂ := b5e42 X0
               grind)
            | exact superpose b5e42 b5e18866
            | (have j0 := b5e18866 X0
               grind)
            | exact resolve b5e18866 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e18866
          have b5e168446 : ∀ X0 : G, (σ (M.op (M.op X0 y) x)) ≠ (σ (M.op (M.op X0 y) x)) ∨ (σ (M.op (M.op X0 y) x)) = (M.op (σ y) (σ (M.op (M.op X0 y) x))) ∨ y = (k y (M.op (M.op X0 y) x)) := by
            intro X0
            first
            | (have i₁ := b5e996 y (M.op (M.op X0 y) x)
               have i₂ := b5e18911 X0
               grind)
            | exact superpose b5e18911 b5e996
            | (have j0 := b5e996 y (M.op (M.op X0 y) x)
               have j1 := b5e18911 X0
               grind)
            | exact resolve b5e996 b5e18911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e996 b5e18911
          have b5e168459 : ∀ X0 : G, (σ (M.op (M.op X0 y) x)) = (M.op (σ y) (σ (M.op (M.op X0 y) x))) ∨ y = (k y (M.op (M.op X0 y) x)) := by
            intro X0
            first
            | (have j0 := b5e168446 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e168446
          have b5e1402974 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e168459 (M.op x x)
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e168459
            | exact resolve b5e168459 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31 b5e168459
          have b5e1403081 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e2531 (σ x)
               have i₂ := b5e1402974
               grind)
            | exact superpose b5e1402974 b5e2531
            | exact resolve b5e2531 b5e1402974
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2531 b5e1402974
          have b5e1403176 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b5e1403081
               have i₂ := b5e2328
               grind)
            | exact superpose b5e2328 b5e1403081
            | exact resolve b5e1403081 b5e2328
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2328 b5e1403081
          have b5e1403186 : y = (k y x) := by
            first
            | (have r₁ := b5e1403176
               have r₂ := b5e24
               grind)
            | exact resolve b5e1403176 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1403176
          have b5e1403406 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e5589 x
               have i₂ := b5e1403186
               grind)
            | exact superpose b5e1403186 b5e5589
            | (have j0 := b5e5589 x
               grind)
            | exact resolve b5e5589 b5e1403186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5589 b5e1403186
          have b5e1404737 : (σ y) = (M.op (σ (k x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1403406
               have i₂ := b5e129 x y
               grind)
            | exact superpose b5e129 b5e1403406
            | (have j1 := b5e129 (k x y) y
               grind)
            | exact resolve b5e1403406 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129 b5e1403406
          have b5e1404747 : (σ y) = (M.op (σ (k x y)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1404737
               have r₂ := b5e24
               grind)
            | exact resolve b5e1404737 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1404737
          have b5e1404748 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e1404747
               have i₂ := b5e57
               grind)
            | exact superpose b5e57 b5e1404747
            | exact resolve b5e1404747 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57 b5e1404747
          have b5e1404749 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e1404748
               have r₂ := b5e24
               grind)
            | exact resolve b5e1404748 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1404748
          have b5e1404847 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b5e30 (σ y) (σ x)
               have i₂ := b5e1404749
               grind)
            | exact superpose b5e1404749 b5e30
            | exact resolve b5e30 b5e1404749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e1404909 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1404847
               have i₂ := b5e1404749
               grind)
            | exact superpose b5e1404749 b5e1404847
            | exact resolve b5e1404847 b5e1404749
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1404749 b5e1404847
          have b5e1404949 : False := by grind
          exact b5e1404949
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e37 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b6e38 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e37
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e37
          | exact resolve b6e37 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e72 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          first
          | (have j0 := b6e69 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e73 : (σ (M.op x y)) ≠ (σ (k x y)) := by
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
        have b6e82 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e72 y x
             grind)
          | exact superpose b6e72 b6e73
          | (have j1 := b6e72 y x
             grind)
          | exact resolve b6e73 b6e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72 b6e73
        have b6e85 : y = (M.op x y) := by grind
        clear b6e82
        have b6e87 : False := by grind
        exact b6e87
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X0 X2)) X0) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
          have b7e34 : ∀ X0 X3 : G, (M.op (M.op X0 (M.op X0 X3)) X0) = X0 := by
            intro X0 X3
            first
            | (have i₁ := b7e13 X0 (M.op (M.op x X0) (M.op X0 x)) X3
               have i₂ := b7e13 X0 x x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e34 (σ x) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e37
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e37
            | exact resolve b7e37 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e50 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e51 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have i₁ := b7e17 (σ y) (σ x)
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e17
            | (have j0 := b7e17 (σ y) (σ x)
               grind)
            | (have r₁ := b7e17 (σ y) (σ x)
               have r₂ := b7e44
               grind)
            | exact resolve b7e17 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e56 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
          clear b7e51
          have b7e57 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e50
          have b7e60 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e56
            | exact resolve b7e56 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e61 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e23
               grind)
            | exact resolve b7e57 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e62 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e60
            | exact resolve b7e60 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e63 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e61
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e61
            | exact resolve b7e61 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e64 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e63
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e63
            | exact resolve b7e63 b7e44
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
          have b7e80 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e83 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e80 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e80
          have b7e87 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e88 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e21
               grind)
            | exact resolve b7e87 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e90 : x = (M.op x y) := by
            first
            | (have r₁ := b7e88
               have r₂ := b7e22
               grind)
            | exact resolve b7e88 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e106 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
            intro X0
            first
            | (have i₁ := b7e13 y x X0
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e13
            | exact resolve b7e13 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e356 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op (M.op (M.op x (M.op y X0)) y) (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e34 (M.op x (M.op y X0)) y
               have i₂ := b7e106 X0
               grind)
            | exact superpose b7e106 b7e34
            | exact resolve b7e34 b7e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e362 : ∀ X0 : G, (M.op x (M.op y X0)) = (M.op y (M.op x (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b7e356 X0
               have i₂ := b7e106 X0
               grind)
            | exact superpose b7e106 b7e356
            | exact resolve b7e356 b7e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106 b7e356
          have b7e1154 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by grind
          clear b7e62
          have b7e1170 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1154
               have i₂ := b7e19 y x
               grind)
            | exact superpose b7e19 b7e1154
            | exact resolve b7e1154 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1154
          have b7e1174 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e1170
               have i₂ := b7e44
               grind)
            | exact superpose b7e44 b7e1170
            | exact resolve b7e1170 b7e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44 b7e1170
          have b7e1593 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1174
               grind)
            | exact superpose b7e1174 b7e14
            | exact resolve b7e14 b7e1174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1174
          have b7e1625 : (σ x) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e1593
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1593
            | exact resolve b7e1593 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1593
          have b7e1670 : (k y x) = (τ (σ x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b7e14 (k y x)
               have i₂ := b7e1625
               grind)
            | exact superpose b7e1625 b7e14
            | exact resolve b7e14 b7e1625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1625
          have b7e1702 : y = (k y x) ∨ x = (k y x) := by
            first
            | (have i₁ := b7e1670
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1670
            | exact resolve b7e1670 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1670
          have b7e1820 : y = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e1702
               have i₂ := b7e83 x y
               grind)
            | exact superpose b7e83 b7e1702
            | (have j1 := b7e83 x y
               grind)
            | exact resolve b7e1702 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e1702
          have b7e1828 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b7e1820
          have b7e1864 : (M.op x y) = (M.op y (M.op x y)) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e362 x
               have i₂ := b7e1828
               grind)
            | exact superpose b7e1828 b7e362
            | exact resolve b7e362 b7e1828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e362 b7e1828
          have b7e1885 : x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b7e1864
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e1864
            | exact resolve b7e1864 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e1864
          have b7e1886 : x = (M.op y x) := by grind
          clear b7e1885
          have b7e1950 : y = (M.op (M.op y x) y) := by
            first
            | (have i₁ := b7e34 y x
               have i₂ := b7e1886
               grind)
            | exact superpose b7e1886 b7e34
            | exact resolve b7e34 b7e1886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1964 : y = (M.op x y) := by
            first
            | (have i₁ := b7e1950
               have i₂ := b7e1886
               grind)
            | exact superpose b7e1886 b7e1950
            | exact resolve b7e1950 b7e1886
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1886 b7e1950
          have b7e1972 : False := by grind
          exact b7e1972
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e170 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e20
            | (have j1 := b8e65 x y
               grind)
            | exact resolve b8e20 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e211 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e170
               have r₂ := b8e23
               grind)
            | exact resolve b8e170 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170
          have b8e216 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e211
               have r₂ := b8e24
               grind)
            | exact resolve b8e211 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211
          have b8e217 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e216
               have i₂ := b8e76 y x
               grind)
            | exact superpose b8e76 b8e216
            | (have j1 := b8e76 y x
               grind)
            | exact resolve b8e216 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e216
          have b8e220 : y = (M.op x y) := by grind
          clear b8e217
          have b8e222 : False := by grind
          exact b8e222

/-- `Equation2722`: `x = ((y ◇ x) ◇ (z ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = m(Y,X) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_y_pxx_pxy_Equation2722 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2722 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2722.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = (M.op y y) := by grind
        have b0e21 : (σ x) = (M.op (σ y) (σ y)) := by grind
        have b0e22 : y = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e40 : ∀ X0 : G, (M.op (M.op (M.op x X0) y) x) = X0 := by
          intro X0
          first
          | (have i₁ := b0e12 X0 x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e109 : x = (M.op (M.op y y) x) := by
          first
          | (have i₁ := b0e40 x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e40
          | exact resolve b0e40 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e119 : x = (M.op x x) := by
          first
          | (have i₁ := b0e109
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e109
          | exact resolve b0e109 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e109
        have b0e121 : x = y := by
          first
          | (have i₁ := b0e119
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e119
          | exact resolve b0e119 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e119
        have b0e122 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e121
             grind)
          | exact superpose b0e121 b0e19
          | exact resolve b0e19 b0e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e121
        have b0e130 : (σ x) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e122
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e122
          | exact resolve b0e122 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e122
        have b0e131 : False := by grind
        exact b0e131
      · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b1e21 : x = (M.op y y) := by grind
          have b1e23 : y ≠ (M.op x x) := by grind
          have b1e24 : (M.op x y) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e38 : ∀ X0 : G, y = (M.op (M.op (M.op y y) (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b1e13 y x X0
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
               have i₂ := b1e13 X0 X1 (M.op X2 (M.op X1 X0))
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e49 : y = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b1e38 x
               have i₂ := b1e45 x x (M.op y y)
               grind)
            | exact superpose b1e45 b1e38
            | exact resolve b1e38 b1e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e45
          have b1e51 : y = (M.op x x) := by
            first
            | (have i₁ := b1e49
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e49
            | exact resolve b1e49 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49
          have b1e52 : False := by grind
          exact b1e52
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : x = (M.op y y) := by grind
          have b2e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
          have b2e23 : y ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b2e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e29 X0 X1
               grind)
            | exact superpose b2e29 b2e14
            | exact resolve b2e14 b2e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e35 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 y)) X0) := by
            intro X0
            first
            | (have i₁ := b2e13 y y X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (M.op X0 (σ y))) X0) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) (σ y) X0
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e38 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 y y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e39 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ x)) (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 (σ y) (σ y)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e13
            | exact resolve b2e13 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op (M.op X3 X0) (M.op X1 X3))) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 X1 (M.op (M.op X3 X0) (M.op X1 X3))
               have i₂ := b2e13 X0 X3 X1
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
               have i₂ := b2e13 X0 X1 (M.op X2 (M.op X1 X0))
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e42 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e37 X0 X1 X2 x
               have i₂ := b2e41 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
               grind)
            | exact superpose b2e41 b2e37
            | exact resolve b2e37 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37
          have b2e43 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b2e36 x
               have i₂ := b2e41 (σ y) x (σ x)
               grind)
            | exact superpose b2e41 b2e36
            | exact resolve b2e36 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36
          have b2e44 : y = (M.op y x) := by
            first
            | (have i₁ := b2e35 x
               have i₂ := b2e41 y x x
               grind)
            | exact superpose b2e41 b2e35
            | exact resolve b2e35 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e35
          have b2e45 : ∀ X0 : G, (M.op (M.op (M.op x X0) y) y) = X0 := by
            intro X0
            first
            | (have i₁ := b2e13 X0 x y
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e13
            | exact resolve b2e13 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e17 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e75 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e17 X0 X1
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e17 X0 X0
               have i₂ := b2e18 X0 X1
               grind)
            | exact superpose b2e18 b2e17
            | (have j0 := b2e17 X0 X1
               have j1 := b2e18 X0 X1
               grind)
            | (have r₁ := b2e17 X1 X1
               have r₂ := b2e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b2e17 X1 X1
               have r₂ := b2e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b2e17 X0 X1
               have r₂ := b2e18 X0 X1
               grind)
            | exact resolve b2e17 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e83 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X1 X2
               have i₂ := b2e18 X1 X0
               grind)
            | (have i₁ := b2e13 X0 X1 X2
               have i₂ := b2e18 X0 X1
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X1 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e90 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e75 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75
          have b2e91 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e90 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e90
          have b2e94 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e83 X0 X1 x
               have i₂ := b2e41 X1 x (M.op X0 X1)
               grind)
            | exact superpose b2e41 b2e83
            | (have j0 := b2e83 X0 X1 x
               grind)
            | exact resolve b2e83 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83
          have b2e98 : y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b2e38 y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e38
            | exact resolve b2e38 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e103 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op y X0) x))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 y (M.op (M.op y X0) x) X1
               have i₂ := b2e38 X0
               grind)
            | exact superpose b2e38 b2e13
            | exact resolve b2e13 b2e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e104 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) x) X0) := by
            intro X0
            first
            | (have i₁ := b2e103 X0 x
               have i₂ := b2e41 (M.op (M.op y X0) x) x X0
               grind)
            | exact superpose b2e41 b2e103
            | exact resolve b2e103 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e103
          have b2e142 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op X0 (σ x)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e41 (σ y) (σ y) X0
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e41
            | exact resolve b2e41 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e143 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (σ y)) (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e41 (σ x) (σ y) X0
               have i₂ := b2e43
               grind)
            | exact superpose b2e43 b2e41
            | exact resolve b2e41 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e152 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X0 x
               have i₂ := b2e41 X0 x (M.op X0 X1)
               grind)
            | exact superpose b2e41 b2e13
            | exact resolve b2e13 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e153 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 (M.op (M.op X2 X1) X0) X1 X2
               have i₂ := b2e41 X0 (M.op X2 X1) X1
               grind)
            | exact superpose b2e41 b2e13
            | exact resolve b2e13 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e154 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) y) := by
            intro X0
            first
            | (have i₁ := b2e38 (M.op x X0)
               have i₂ := b2e41 X0 x y
               grind)
            | exact superpose b2e41 b2e38
            | exact resolve b2e38 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e38
          have b2e155 : ∀ X0 : G, (M.op y X0) = (M.op (M.op X0 x) y) := by
            intro X0
            first
            | (have i₁ := b2e45 (M.op y X0)
               have i₂ := b2e41 X0 y x
               grind)
            | exact superpose b2e41 b2e45
            | exact resolve b2e45 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e45
          have b2e205 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) y) X0) := by
            intro X0
            first
            | (have i₁ := b2e42 X0 y (M.op x x)
               have i₂ := b2e98
               grind)
            | exact superpose b2e98 b2e42
            | exact resolve b2e42 b2e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e206 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op X2 X3) (M.op X0 X1)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e42 X3 X2 (M.op X1 (M.op X2 X0))
               have i₂ := b2e41 X0 X2 X1
               grind)
            | exact superpose b2e41 b2e42
            | exact resolve b2e42 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e212 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X2 X1) X0)) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 (M.op (M.op X2 X1) X0) X1 X2
               have i₂ := b2e41 X0 (M.op X2 X1) X1
               grind)
            | exact superpose b2e41 b2e42
            | exact resolve b2e42 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e230 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e206 X0 X1 X2 X3
               have i₂ := b2e153 (M.op X2 X3) (M.op X0 X1) X3
               grind)
            | (have i₁ := b2e206 X0 X1 X2 X3
               have i₂ := b2e153 X3 (M.op X0 X1) (M.op X2 X3)
               grind)
            | exact superpose b2e153 b2e206
            | exact resolve b2e206 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e206
          have b2e231 : ∀ X0 : G, (M.op x x) = (M.op (M.op X0 y) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b2e205 X0
               have i₂ := b2e153 (M.op y X0) y X0
               grind)
            | (have i₁ := b2e205 X0
               have i₂ := b2e153 X0 y (M.op y X0)
               grind)
            | exact superpose b2e153 b2e205
            | exact resolve b2e205 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e205
          have b2e284 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (σ x)) = (M.op (M.op (M.op (σ y) X1) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e42 X1 (σ y) (M.op (M.op (σ y) X0) (σ x))
               have i₂ := b2e39 X0
               grind)
            | exact superpose b2e39 b2e42
            | exact resolve b2e42 b2e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39
          have b2e287 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (σ x)) = (M.op (M.op X1 X0) (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e284 X0 X1
               have i₂ := b2e153 (M.op (σ y) X1) X0 X1
               grind)
            | (have i₁ := b2e284 X0 X1
               have i₂ := b2e153 X1 X0 (M.op (σ y) X1)
               grind)
            | exact superpose b2e153 b2e284
            | exact resolve b2e284 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e284
          have b2e336 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e19 X0 X0
               have i₂ := b2e53 (σ X0)
               grind)
            | exact superpose b2e53 b2e19
            | (have j1 := b2e53 (σ X0)
               grind)
            | exact resolve b2e19 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e337 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e29 X0 (τ X0)
               have i₂ := b2e53 (τ X0)
               grind)
            | exact superpose b2e53 b2e29
            | (have j1 := b2e53 (τ X0)
               grind)
            | exact resolve b2e29 b2e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e53
          have b2e339 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b2e337 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e337
            | (have j0 := b2e337 X0
               grind)
            | exact resolve b2e337 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e337
          have b2e465 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) (M.op y (M.op X0 y))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e40 x X0 X1 y
               have i₂ := b2e44
               grind)
            | exact superpose b2e44 b2e40
            | exact resolve b2e40 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40 b2e44
          have b2e839 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
            intro X0
            grind
          clear b2e34
          have b2e845 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e839 X0
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e839
            | exact resolve b2e839 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e839
          have b2e1024 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e91
          have b2e1114 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e41 X0 X1 X0
               have i₂ := b2e94 X1 X0
               grind)
            | exact superpose b2e94 b2e41
            | (have j1 := b2e94 X1 X0
               grind)
            | exact resolve b2e41 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e94
          have b2e1182 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e1114 X0 X1
               have j1 := b2e1024 X0 X1
               grind)
            | (have r₁ := b2e1114 X0 X1
               have r₂ := b2e1024 X0 X1
               grind)
            | (have r₁ := b2e1114 X1 X1
               have r₂ := b2e1024 X1 X1
               grind)
            | (have r₁ := b2e1114 (M.op X0 X1) X0
               have r₂ := b2e1024 X0 X1
               grind)
            | exact resolve b2e1114 b2e1024
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1024 b2e1114
          have b2e1598 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X0) (M.op X2 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e153 X3 X0 (M.op X2 X1)
               have i₂ := b2e153 X2 X1 X0
               grind)
            | (have i₁ := b2e153 X3 X0 (M.op X2 X1)
               have i₂ := b2e153 X0 X1 X2
               grind)
            | exact superpose b2e153 b2e153
            | exact resolve b2e153 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e1703 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op (M.op (M.op x X0) X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e155 (M.op X1 X0)
               have i₂ := b2e153 X1 X0 x
               grind)
            | (have i₁ := b2e155 (M.op X1 X0)
               have i₂ := b2e153 x X0 X1
               grind)
            | exact superpose b2e153 b2e155
            | exact resolve b2e155 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e155
          have b2e1710 : ∀ X0 X1 : G, (M.op y (M.op X1 X0)) = (M.op (M.op y X1) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e1703 X0 X1
               have i₂ := b2e153 (M.op x X0) X1 y
               grind)
            | (have i₁ := b2e1703 X0 X1
               have i₂ := b2e153 y X1 (M.op x X0)
               grind)
            | exact superpose b2e153 b2e1703
            | exact resolve b2e1703 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1703
          have b2e8979 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ x) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b2e143 (M.op X0 (σ y))
               have i₂ := b2e143 X0
               grind)
            | exact superpose b2e143 b2e143
            | exact resolve b2e143 b2e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e143
          have b2e9070 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ y))) = (M.op (M.op (σ y) X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b2e8979 X0
               have i₂ := b2e153 (σ x) X0 (σ y)
               grind)
            | (have i₁ := b2e8979 X0
               have i₂ := b2e153 (σ y) X0 (σ x)
               grind)
            | exact superpose b2e153 b2e8979
            | exact resolve b2e8979 b2e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e153 b2e8979
          have b2e9769 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e9806 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) X1) = X2 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e42 X1 X1 X2
               have i₂ := b2e1182 X0 X1
               grind)
            | (have i₁ := b2e42 X0 X1 X2
               have i₂ := b2e1182 (M.op X1 X0) X1
               grind)
            | exact superpose b2e1182 b2e42
            | (have j1 := b2e1182 X0 X1
               grind)
            | exact resolve b2e42 b2e1182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e42
          have b2e9854 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e845 X1
               have i₂ := b2e1182 X0 (σ X1)
               grind)
            | (have i₁ := b2e845 X0
               have i₂ := b2e1182 (M.op (σ X0) (σ X0)) X1
               grind)
            | exact superpose b2e1182 b2e845
            | (have j1 := b2e1182 X0 (σ X1)
               grind)
            | exact resolve b2e845 b2e1182
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e845 b2e1182
          have b2e9932 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e9769 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9769
          have b2e12166 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) x) = (M.op (M.op X1 (M.op y (M.op X2 y))) (M.op X0 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e212 X1 (M.op y (M.op X2 y)) (M.op (M.op X2 X0) x)
               have i₂ := b2e465 X2 X0
               grind)
            | exact superpose b2e465 b2e212
            | exact resolve b2e212 b2e465
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e465
          have b2e12174 : ∀ X0 X2 : G, (M.op (M.op X2 X0) x) = (M.op (M.op X2 y) (M.op X0 y)) := by
            intro X0 X2
            first
            | (have i₁ := b2e12166 X0 x X2
               have i₂ := b2e230 y (M.op X2 y) X0 x
               grind)
            | exact superpose b2e230 b2e12166
            | exact resolve b2e12166 b2e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e230 b2e12166
          have b2e50688 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b2e336 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e336
          have b2e51566 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e339 (σ X0)
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e339
            | exact resolve b2e339 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e339
          have b2e51626 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e51566 X0
               have i₂ := b2e19 X0 X0
               grind)
            | exact superpose b2e19 b2e51566
            | (have j0 := b2e51566 X0
               grind)
            | exact resolve b2e51566 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e51566
          have b2e364875 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e50688 (τ X0)
               have i₂ := b2e29 X0 (τ X0)
               grind)
            | exact superpose b2e29 b2e50688
            | (have j0 := b2e50688 (τ X0)
               grind)
            | exact resolve b2e50688 b2e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29
          have b2e364879 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e364875 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e364875
            | (have j0 := b2e364875 X0
               grind)
            | exact resolve b2e364875 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e364875
          have b2e364889 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e364879 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e364879
            | (have j0 := b2e364879 X0
               grind)
            | exact resolve b2e364879 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e364879
          have b2e394864 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e9854 (σ X0) X1
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e9854
            | (have j0 := b2e9854 (σ X0) X1
               grind)
            | exact resolve b2e9854 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e394881 : ∀ X0 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b2e364889 (τ X0)
               have i₂ := b2e9854 X0 (τ X0)
               grind)
            | exact superpose b2e9854 b2e364889
            | (have j0 := b2e364889 (τ X0)
               have j1 := b2e9854 X0 (τ X0)
               grind)
            | (have r₁ := b2e364889 (τ X0)
               have r₂ := b2e9854 X0 (τ X0)
               grind)
            | exact resolve b2e364889 b2e9854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9854 b2e364889
          have b2e394898 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k X0 (σ (τ X0))) = (M.op X0 (σ (τ X0))) := by
            intro X0
            first
            | (have j0 := b2e394881 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394881
          have b2e394905 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b2e394898 X0
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e394898
            | (have j0 := b2e394898 X0
               grind)
            | exact resolve b2e394898 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394898
          have b2e394910 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e394864 X0 X1
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e394864
            | (have j0 := b2e394864 X0 X1
               grind)
            | exact resolve b2e394864 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394864
          have b2e517769 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b2e394905 (σ X0)
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e394905
            | (have j0 := b2e394905 (σ X0)
               grind)
            | exact resolve b2e394905 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394905
          have b2e517932 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e517769 X0
               have i₂ := b2e19 X0 X0
               grind)
            | exact superpose b2e19 b2e517769
            | (have j0 := b2e517769 X0
               grind)
            | exact resolve b2e517769 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e517769
          have b2e521597 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ (k X0 X1))) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e152 (σ X0) (σ X1)
               have i₂ := b2e394910 X0 X1
               grind)
            | exact superpose b2e394910 b2e152
            | (have j1 := b2e394910 X0 X1
               grind)
            | exact resolve b2e152 b2e394910
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e394910
          have b2e568600 : (M.op (σ y) (σ x)) = (M.op (σ (k x x)) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e142 (σ x)
               have i₂ := b2e517932 x
               grind)
            | exact superpose b2e517932 b2e142
            | (have j1 := b2e517932 x
               grind)
            | exact resolve b2e142 b2e517932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e517932
          have b2e568654 : (σ y) = (M.op (σ (k x x)) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e568600
               have i₂ := b2e43
               grind)
            | exact superpose b2e43 b2e568600
            | exact resolve b2e568600 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e568600
          have b2e571932 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e521597 X0 X0
               have i₂ := b2e51626 X0
               grind)
            | exact superpose b2e51626 b2e521597
            | (have j0 := b2e521597 X0 X0
               have j1 := b2e51626 X0
               grind)
            | exact resolve b2e521597 b2e51626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e572014 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have j0 := b2e571932 X0
               have j1 := b2e9932 X0 X0
               grind)
            | (have r₁ := b2e571932 x
               have r₂ := b2e9932 x x
               grind)
            | exact resolve b2e571932 b2e9932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9932 b2e571932
          have b2e627070 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e568654
               have i₂ := b2e51626 x
               grind)
            | exact superpose b2e51626 b2e568654
            | (have j1 := b2e51626 x
               grind)
            | exact resolve b2e568654 b2e51626
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e51626 b2e568654
          have b2e627114 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x x) := by grind
          clear b2e627070
          have b2e632550 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (k X0 X0) = X0 := by
            intro X0
            first
            | (have i₁ := b2e152 (σ X0) (σ (M.op X0 X0))
               have i₂ := b2e572014 X0
               grind)
            | exact superpose b2e572014 b2e152
            | (have j1 := b2e572014 X0
               grind)
            | exact resolve b2e152 b2e572014
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e152 b2e572014
          have b2e662534 : (M.op (σ y) (σ x)) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (k x x) := by
            first
            | (have i₁ := b2e142 (σ x)
               have i₂ := b2e632550 x
               grind)
            | exact superpose b2e632550 b2e142
            | (have j1 := b2e632550 x
               grind)
            | exact resolve b2e142 b2e632550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e632550
          have b2e662588 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (k x x) := by
            first
            | (have i₁ := b2e662534
               have i₂ := b2e43
               grind)
            | exact superpose b2e43 b2e662534
            | exact resolve b2e662534 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e662534
          have b2e983098 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) x) y) = X1 ∨ (M.op (M.op X0 y) y) = (k (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e9806 (M.op X0 y) y X1
               have i₂ := b2e12174 X1 X0
               grind)
            | exact superpose b2e12174 b2e9806
            | (have j0 := b2e9806 (M.op X0 y) y x
               grind)
            | exact resolve b2e9806 b2e12174
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9806 b2e12174
          have b2e983287 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op x X1)) = X1 ∨ (M.op (M.op X0 y) y) = (k (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e983098 X0 X1
               have i₂ := b2e1598 X0 X1 x y
               grind)
            | exact superpose b2e1598 b2e983098
            | (have j0 := b2e983098 X0 X1
               grind)
            | exact resolve b2e983098 b2e1598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e983098
          have b2e983335 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = X1 ∨ (M.op (M.op X0 y) y) = (k (M.op X0 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e983287 X0 X1
               have i₂ := b2e1710 X1 X0
               grind)
            | exact superpose b2e1710 b2e983287
            | (have j0 := b2e983287 X0 X1
               grind)
            | exact resolve b2e983287 b2e1710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1710 b2e983287
          have b2e983347 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op X0 y) y) ∨ (M.op y (M.op X0 X1)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e983335 X0 X1
               have i₂ := b2e154 X0
               grind)
            | exact superpose b2e154 b2e983335
            | (have j0 := b2e983335 X0 X1
               grind)
            | exact resolve b2e983335 b2e154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e154 b2e983335
          have b2e1259062 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 y) ∨ (M.op x X1) = (k (M.op X1 y) y) := by
            intro X0 X1
            first
            | (have i₁ := b2e41 X0 X1 y
               have i₂ := b2e983347 X1 X0
               grind)
            | exact superpose b2e983347 b2e41
            | (have j1 := b2e983347 X1 X1
               grind)
            | exact resolve b2e41 b2e983347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e41 b2e983347
          have b2e1731225 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) y) X0) ∨ (M.op x x) = (k (M.op x y) y) := by
            intro X0
            first
            | (have i₁ := b2e104 X0
               have i₂ := b2e1259062 (M.op y X0) x
               grind)
            | exact superpose b2e1259062 b2e104
            | (have j1 := b2e1259062 X0 x
               grind)
            | exact resolve b2e104 b2e1259062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e104 b2e1259062
          have b2e1731256 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y X0)) ∨ (M.op x x) = (k (M.op x y) y) := by
            intro X0
            first
            | (have i₁ := b2e1731225 X0
               have i₂ := b2e1598 y X0 y X0
               grind)
            | (have i₁ := b2e1731225 (M.op x x)
               have i₂ := b2e1598 y x x (M.op y (M.op x x))
               grind)
            | exact superpose b2e1598 b2e1731225
            | exact resolve b2e1731225 b2e1598
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1598 b2e1731225
          have b2e1731278 : y = (M.op x x) ∨ (M.op x x) = (k (M.op x y) y) := by
            first
            | (have i₁ := b2e1731256 x
               have i₂ := b2e231 x
               grind)
            | exact superpose b2e231 b2e1731256
            | exact resolve b2e1731256 b2e231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e231 b2e1731256
          have b2e1731288 : (M.op x x) = (k (M.op x y) y) := by
            first
            | (have r₁ := b2e1731278
               have r₂ := b2e23
               grind)
            | exact resolve b2e1731278 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1731278
          have b2e1732215 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x x))) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b2e521597 (M.op x y) y
               have i₂ := b2e1731288
               grind)
            | exact superpose b2e1731288 b2e521597
            | exact resolve b2e521597 b2e1731288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e521597 b2e1731288
          have b2e1732232 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x x))) := by
            first
            | (have r₁ := b2e1732215
               have r₂ := b2e23
               grind)
            | exact resolve b2e1732215 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1732215
          have b2e1736380 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x x))) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b2e212 X0 (σ (M.op x x)) (σ (M.op x y))
               have i₂ := b2e1732232
               grind)
            | exact superpose b2e1732232 b2e212
            | exact resolve b2e212 b2e1732232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e212 b2e1732232
          have b2e1736408 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ (M.op x x))) (σ x)) := by
            first
            | (have i₁ := b2e1736380 x
               have i₂ := b2e287 (σ (M.op x x)) x
               grind)
            | exact superpose b2e287 b2e1736380
            | exact resolve b2e1736380 b2e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e287 b2e1736380
          have b2e1736421 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x x)) (σ y))) := by
            first
            | (have i₁ := b2e1736408
               have i₂ := b2e9070 (σ (M.op x x))
               grind)
            | exact superpose b2e9070 b2e1736408
            | exact resolve b2e1736408 b2e9070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e9070 b2e1736408
          have b2e1759791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k x x) := by
            first
            | (have i₁ := b2e1736421
               have i₂ := b2e662588
               grind)
            | exact superpose b2e662588 b2e1736421
            | exact resolve b2e1736421 b2e662588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e662588
          have b2e1759792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b2e1736421
               have i₂ := b2e627114
               grind)
            | exact superpose b2e627114 b2e1736421
            | exact resolve b2e1736421 b2e627114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e627114 b2e1736421
          have b2e1759854 : x = (M.op x x) := by
            first
            | (have r₁ := b2e1759792
               have r₂ := b2e20
               grind)
            | exact resolve b2e1759792 b2e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1759792
          have b2e1759855 : x = (k x x) := by
            first
            | (have r₁ := b2e1759791
               have r₂ := b2e20
               grind)
            | exact resolve b2e1759791 b2e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1759791
          have b2e1763787 : y = (M.op x y) := by
            first
            | (have i₁ := b2e98
               have i₂ := b2e1759854
               grind)
            | exact superpose b2e1759854 b2e98
            | exact resolve b2e98 b2e1759854
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e98 b2e1759854
          have b2e1770172 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b2e50688 x
               have i₂ := b2e1759855
               grind)
            | exact superpose b2e1759855 b2e50688
            | (have j0 := b2e50688 x
               grind)
            | exact resolve b2e50688 b2e1759855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e50688 b2e1759855
          have b2e1770210 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b2e1770172
          have b2e1808088 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b2e142 (σ x)
               have i₂ := b2e1770210
               grind)
            | exact superpose b2e1770210 b2e142
            | exact resolve b2e142 b2e1770210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e142 b2e1770210
          have b2e1808376 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b2e1808088
               have i₂ := b2e43
               grind)
            | exact superpose b2e43 b2e1808088
            | exact resolve b2e1808088 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43 b2e1808088
          have b2e1837652 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e1808376
               grind)
            | exact superpose b2e1808376 b2e20
            | exact resolve b2e20 b2e1808376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1808376
          have b2e1837945 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b2e1837652
               have i₂ := b2e1763787
               grind)
            | exact superpose b2e1763787 b2e1837652
            | exact resolve b2e1837652 b2e1763787
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1763787 b2e1837652
          have b2e1837946 : False := by grind
          exact b2e1837946
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : x = (M.op y y) := by grind
          have b3e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b3e23 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          have b3e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : y = (k x y) := by grind
          have b3e35 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 x x X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
               have i₂ := b3e13 X0 X1 (M.op X2 (M.op X1 X0))
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e42 : x = (M.op x y) := by
            first
            | (have i₁ := b3e35 x
               have i₂ := b3e40 x x y
               grind)
            | exact superpose b3e40 b3e35
            | exact resolve b3e35 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e35
          have b3e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b3e63 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b3e54
          have b3e64 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b3e63
               have r₂ := b3e22
               grind)
            | exact resolve b3e63 b3e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e63
          have b3e65 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b3e64
               have i₂ := b3e19 x y
               grind)
            | exact superpose b3e19 b3e64
            | exact resolve b3e64 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e64
          have b3e66 : (σ y) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e65
               have i₂ := b3e26
               grind)
            | exact superpose b3e26 b3e65
            | exact resolve b3e65 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e65
          have b3e113 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op X0 (σ x))) X0) := by
            intro X0
            first
            | (have i₁ := b3e13 (σ x) (σ x) X0
               have i₂ := b3e66
               grind)
            | exact superpose b3e66 b3e13
            | exact resolve b3e13 b3e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e66
          have b3e115 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e113 x
               have i₂ := b3e40 (σ x) x (σ y)
               grind)
            | exact superpose b3e40 b3e113
            | exact resolve b3e113 b3e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40 b3e113
          have b3e118 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e115
               grind)
            | exact superpose b3e115 b3e20
            | exact resolve b3e20 b3e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e115
          have b3e122 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e118
               have i₂ := b3e42
               grind)
            | exact superpose b3e42 b3e118
            | exact resolve b3e118 b3e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e42 b3e118
          have b3e123 : False := by grind
          exact b3e123
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b4e22 : x = (M.op y y) := by grind
            have b4e25 : y ≠ (M.op x x) := by grind
            have b4e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e38 : ∀ X0 : G, y = (M.op (M.op (M.op y y) (M.op X0 x)) X0) := by
              intro X0
              first
              | (have i₁ := b4e14 y x X0
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e43 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b4e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b4e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b4e14 b4e14
              | exact resolve b4e14 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e46 : y = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b4e38 x
                 have i₂ := b4e43 x x (M.op y y)
                 grind)
              | exact superpose b4e43 b4e38
              | exact resolve b4e38 b4e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e38 b4e43
            have b4e48 : y = (M.op x x) := by
              first
              | (have i₁ := b4e46
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e46
              | exact resolve b4e46 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e46
            have b4e49 : False := by grind
            exact b4e49
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b5e26 : (M.op x y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b5e14 X0 X1 X2
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b5e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e40 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e36 X0 X1 X2 x
                 have i₂ := b5e39 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b5e39 b5e36
              | exact resolve b5e36 b5e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e36 b5e39
            have b5e204 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) X0) (M.op (σ y) (σ x))) X0) := by
              intro X0
              first
              | (have i₁ := b5e40 X0 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e40
              | exact resolve b5e40 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e224 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e204 x
                 have i₂ := b5e40 x (σ x) (σ y)
                 grind)
              | exact superpose b5e40 b5e204
              | exact resolve b5e204 b5e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e40 b5e204
            have b5e251 : x = (τ (σ y)) := by
              first
              | (have i₁ := b5e15 x
                 have i₂ := b5e224
                 grind)
              | exact superpose b5e224 b5e15
              | exact resolve b5e15 b5e224
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e224
            have b5e252 : x = y := by
              first
              | (have i₁ := b5e251
                 have i₂ := b5e15 y
                 grind)
              | exact superpose b5e15 b5e251
              | exact resolve b5e251 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e251
            have b5e258 : (M.op y y) ≠ (M.op y y) := by
              first
              | (have i₁ := b5e26
                 have i₂ := b5e252
                 grind)
              | exact superpose b5e252 b5e26
              | exact resolve b5e26 b5e252
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e252
            have b5e265 : False := by grind
            exact b5e265
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b6e21 : x = (M.op y y) := by grind
          have b6e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e37 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) y) = X0 := by
            intro X0
            first
            | (have i₁ := b6e13 X0 y y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e97 : y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b6e37 y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e37
            | exact resolve b6e37 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37
          have b6e107 : y = (M.op y y) := by
            first
            | (have i₁ := b6e97
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e97
            | exact resolve b6e97 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e97
          have b6e109 : x = y := by
            first
            | (have i₁ := b6e107
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e107
            | exact resolve b6e107 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e107
          have b6e113 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e109
               grind)
            | exact superpose b6e109 b6e23
            | exact resolve b6e23 b6e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e109
          have b6e119 : False := by grind
          exact b6e119
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : x = (M.op y y) := by grind
            have b7e25 : y ≠ (M.op x x) := by grind
            have b7e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e38 : ∀ X0 : G, y = (M.op (M.op (M.op y y) (M.op X0 x)) X0) := by
              intro X0
              first
              | (have i₁ := b7e14 y x X0
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e43 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b7e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e46 : y = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b7e38 x
                 have i₂ := b7e43 x x (M.op y y)
                 grind)
              | exact superpose b7e43 b7e38
              | exact resolve b7e38 b7e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38 b7e43
            have b7e48 : y = (M.op x x) := by
              first
              | (have i₁ := b7e46
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e46
              | exact resolve b7e46 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46
            have b7e49 : False := by grind
            exact b7e49
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : x = (M.op y y) := by grind
            have b8e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e25 : y ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : y = (k x y) := by grind
            have b8e35 : ∀ X0 : G, y = (M.op (M.op x (M.op X0 y)) X0) := by
              intro X0
              first
              | (have i₁ := b8e14 y y X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b8e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b8e14 X0 X1 X2
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e37 : ∀ X0 : G, (M.op (M.op (M.op y X0) x) y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e14 X0 y y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e39 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b8e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b8e14 b8e14
              | exact resolve b8e14 b8e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e40 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e36 X0 X1 X2 x
                 have i₂ := b8e39 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b8e39 b8e36
              | exact resolve b8e36 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e36
            have b8e41 : y = (M.op y x) := by
              first
              | (have i₁ := b8e35 x
                 have i₂ := b8e39 y x x
                 grind)
              | exact superpose b8e39 b8e35
              | exact resolve b8e35 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e35
            have b8e48 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op y X0) x))) X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e14 y (M.op (M.op y X0) x) X1
                 have i₂ := b8e37 X0
                 grind)
              | exact superpose b8e37 b8e14
              | exact resolve b8e14 b8e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e49 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) x) X0) := by
              intro X0
              first
              | (have i₁ := b8e48 X0 x
                 have i₂ := b8e39 (M.op (M.op y X0) x) x X0
                 grind)
              | exact superpose b8e39 b8e48
              | exact resolve b8e48 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e48
            have b8e77 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e19 X0 (σ y)
                 grind)
              | (have i₁ := b8e23
                 have i₂ := b8e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b8e19 b8e23
              | (have j1 := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e23 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e18 X0 X1
                 have i₂ := b8e19 X0 X1
                 grind)
              | (have i₁ := b8e18 X0 X0
                 have i₂ := b8e19 X0 X1
                 grind)
              | exact superpose b8e19 b8e18
              | (have j0 := b8e18 X0 X1
                 have j1 := b8e19 X0 X1
                 grind)
              | (have r₁ := b8e18 X1 X1
                 have r₂ := b8e19 (M.op X1 X1) X1
                 grind)
              | (have r₁ := b8e18 X1 X1
                 have r₂ := b8e19 (M.op X1 X1) X1
                 grind)
              | (have r₁ := b8e18 X0 X1
                 have r₂ := b8e19 X0 X1
                 grind)
              | exact resolve b8e18 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e88 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 X1 X1 X2
                 have i₂ := b8e19 X1 X0
                 grind)
              | (have i₁ := b8e14 X0 X1 X2
                 have i₂ := b8e19 X0 X1
                 grind)
              | exact superpose b8e19 b8e14
              | (have j1 := b8e19 X1 X0
                 grind)
              | exact resolve b8e14 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b8e79 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e79
            have b8e97 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b8e96 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e96
            have b8e100 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
              intro X0 X1
              first
              | (have i₁ := b8e88 X0 X1 x
                 have i₂ := b8e39 X1 x (M.op X0 X1)
                 grind)
              | exact superpose b8e39 b8e88
              | (have j0 := b8e88 X0 X1 x
                 grind)
              | exact resolve b8e88 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e88
            have b8e141 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e14 (M.op (M.op X2 X1) X0) X1 X2
                 have i₂ := b8e39 X0 (M.op X2 X1) X1
                 grind)
              | exact superpose b8e39 b8e14
              | exact resolve b8e14 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e142 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 y) y) := by
              intro X0
              first
              | (have i₁ := b8e37 (M.op x X0)
                 have i₂ := b8e39 X0 x y
                 grind)
              | exact superpose b8e39 b8e37
              | exact resolve b8e37 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e37
            have b8e170 : ∀ X0 : G, (M.op (M.op y (M.op X0 y)) x) = X0 := by
              intro X0
              first
              | (have i₁ := b8e40 x y X0
                 have i₂ := b8e41
                 grind)
              | exact superpose b8e41 b8e40
              | exact resolve b8e40 b8e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e41
            have b8e234 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x X0)) := by
              intro X0
              first
              | (have i₁ := b8e49 (M.op x X0)
                 have i₂ := b8e39 X0 x y
                 grind)
              | exact superpose b8e39 b8e49
              | exact resolve b8e49 b8e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e49
            have b8e470 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X1 X0) (M.op y (M.op X0 y))) := by
              intro X0 X1
              first
              | (have i₁ := b8e39 x (M.op y (M.op X0 y)) X1
                 have i₂ := b8e170 X0
                 grind)
              | exact superpose b8e170 b8e39
              | exact resolve b8e39 b8e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e170
            have b8e760 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op x (M.op X0 y))) := by
              intro X0
              first
              | (have i₁ := b8e234 (M.op X0 y)
                 have i₂ := b8e142 X0
                 grind)
              | exact superpose b8e142 b8e234
              | exact resolve b8e234 b8e142
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e234
            have b8e845 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X1 X0) X2) ∨ (M.op X0 X0) = (k X0 X2) ∨ (M.op X0 X2) = (k X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e39 X2 X2 X1
                 have i₂ := b8e97 X0 X2
                 grind)
              | (have i₁ := b8e39 X0 X1 X2
                 have i₂ := b8e97 (M.op X1 X0) X1
                 grind)
              | exact superpose b8e97 b8e39
              | (have j1 := b8e97 X0 X2
                 grind)
              | exact resolve b8e39 b8e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e847 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) X2) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e40 X2 X1 X1
                 have i₂ := b8e97 X0 X1
                 grind)
              | (have i₁ := b8e40 X0 X1 X2
                 have i₂ := b8e97 (M.op X2 X1) X1
                 grind)
              | exact superpose b8e97 b8e40
              | (have j1 := b8e97 X0 X1
                 grind)
              | exact resolve b8e40 b8e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e892 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b8e97 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e97
            have b8e912 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 X2)) = X1 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b8e847 X0 X1 X2
                 have i₂ := b8e141 (M.op X1 X2) X0 X2
                 grind)
              | (have i₁ := b8e847 X0 X1 X2
                 have i₂ := b8e141 X2 X0 (M.op X1 X2)
                 grind)
              | exact superpose b8e141 b8e847
              | (have j0 := b8e847 X0 X1 X2
                 grind)
              | exact resolve b8e847 b8e141
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e847
            have b8e970 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have i₁ := b8e39 X0 X1 X0
                 have i₂ := b8e100 X1 X0
                 grind)
              | exact superpose b8e100 b8e39
              | (have j1 := b8e100 X1 X0
                 grind)
              | exact resolve b8e39 b8e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e39 b8e100
            have b8e1035 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b8e970 X0 X1
                 have j1 := b8e892 X0 X1
                 grind)
              | (have r₁ := b8e970 X0 X1
                 have r₂ := b8e892 X0 X1
                 grind)
              | (have r₁ := b8e970 X1 X1
                 have r₂ := b8e892 X1 X1
                 grind)
              | (have r₁ := b8e970 (M.op X0 X1) X0
                 have r₂ := b8e892 X0 X1
                 grind)
              | exact resolve b8e970 b8e892
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e892 b8e970
            have b8e1351 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b8e77 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e77
            have b8e1352 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e1351
                 have r₂ := b8e24
                 grind)
              | exact resolve b8e1351 b8e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1351
            have b8e1353 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e1352
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e1352
              | exact resolve b8e1352 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1352
            have b8e1354 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e1353
                 have i₂ := b8e28
                 grind)
              | exact superpose b8e28 b8e1353
              | exact resolve b8e1353 b8e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e28 b8e1353
            have b8e1364 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) X0) (σ y)) X0) := by
              intro X0
              first
              | (have i₁ := b8e40 X0 (σ y) (σ x)
                 have i₂ := b8e1354
                 grind)
              | exact superpose b8e1354 b8e40
              | exact resolve b8e40 b8e1354
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e40 b8e1354
            have b8e1368 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ y)) (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := b8e1364 X0
                 have i₂ := b8e141 (M.op (σ y) X0) (σ y) X0
                 grind)
              | (have i₁ := b8e1364 X0
                 have i₂ := b8e141 X0 (σ y) (M.op (σ y) X0)
                 grind)
              | exact superpose b8e141 b8e1364
              | exact resolve b8e1364 b8e141
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e141 b8e1364
            have b8e8163 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e1035 X0 (σ y)
                 grind)
              | (have i₁ := b8e23
                 have i₂ := b8e1035 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b8e1035 b8e23
              | (have j1 := b8e1035 X0 (σ y)
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e1035 (σ x) (σ y)
                 grind)
              | exact resolve b8e23 b8e1035
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e1035
            have b8e165416 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (M.op y y) = (k y y) ∨ (M.op y y) = (k y y) := by
              intro X0
              first
              | (have i₁ := b8e142 X0
                 have i₂ := b8e845 y X0 y
                 grind)
              | exact superpose b8e845 b8e142
              | (have j1 := b8e845 y x y
                 grind)
              | exact resolve b8e142 b8e845
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e142 b8e845
            have b8e166135 : ∀ X0 : G, (M.op y X0) = (M.op x X0) ∨ (M.op y y) = (k y y) := by
              intro X0
              first
              | (have j0 := b8e165416 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e165416
            have b8e166308 : ∀ X0 : G, x = (k y y) ∨ (M.op y X0) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b8e166135 X0
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e166135
              | (have j0 := b8e166135 X0
                 grind)
              | exact resolve b8e166135 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e166135
            have b8e167404 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op y (M.op X0 y))) ∨ x = (k y y) := by
              intro X0
              first
              | (have i₁ := b8e760 X0
                 have i₂ := b8e166308 (M.op X0 y)
                 grind)
              | exact superpose b8e166308 b8e760
              | exact resolve b8e760 b8e166308
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e760 b8e166308
            have b8e167761 : y = (M.op x x) ∨ x = (k y y) := by
              first
              | (have i₁ := b8e167404 x
                 have i₂ := b8e470 x x
                 grind)
              | exact superpose b8e470 b8e167404
              | exact resolve b8e167404 b8e470
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e470 b8e167404
            have b8e167877 : x = (k y y) := by
              first
              | (have r₁ := b8e167761
                 have r₂ := b8e25
                 grind)
              | exact resolve b8e167761 b8e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e167761
            have b8e177568 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b8e1368 x
                 have i₂ := b8e912 (σ y) (σ y) x
                 grind)
              | exact superpose b8e912 b8e1368
              | (have j1 := b8e912 (σ y) (σ y) x
                 grind)
              | exact resolve b8e1368 b8e912
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e912 b8e1368
            have b8e178414 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by grind
            clear b8e177568
            have b8e178645 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
              first
              | (have j1 := b8e8163 (σ y)
                 grind)
              | (have r₁ := b8e178414
                 have r₂ := b8e8163 (σ y)
                 grind)
              | exact resolve b8e178414 b8e8163
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e8163 b8e178414
            have b8e179020 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
              first
              | (have i₁ := b8e178645
                 have i₂ := b8e20 y y
                 grind)
              | exact superpose b8e20 b8e178645
              | exact resolve b8e178645 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e178645
            have b8e179284 : (σ x) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b8e179020
                 have i₂ := b8e167877
                 grind)
              | exact superpose b8e167877 b8e179020
              | exact resolve b8e179020 b8e167877
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e167877 b8e179020
            have b8e179470 : False := by grind
            exact b8e179470
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b9e21 : x ≠ (M.op y y) := by grind
          have b9e22 : (M.op x x) = (M.op y x) := by grind
          have b9e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : y = (M.op y x) := by
            first
            | (have i₁ := b9e22
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e22
            | exact resolve b9e22 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e43 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) X0) := by
            intro X0
            first
            | (have i₁ := b9e13 x y X0
               have i₂ := b9e26
               grind)
            | exact superpose b9e26 b9e13
            | exact resolve b9e13 b9e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e50 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b9e13 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
               have i₂ := b9e13 X0 X1 (M.op X2 (M.op X1 X0))
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : x = (M.op y y) := by
            first
            | (have i₁ := b9e43 x
               have i₂ := b9e50 y x y
               grind)
            | exact superpose b9e50 b9e43
            | exact resolve b9e43 b9e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e43 b9e50
          have b9e55 : False := by grind
          exact b9e55
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e23 : (M.op x x) = (M.op y x) := by grind
            have b10e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b10e25 : y ≠ (M.op x x) := by grind
            have b10e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e28 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b10e21
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e21
              | exact resolve b10e21 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : (σ y) = (k (σ x) (σ y)) := by grind
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
            have b10e48 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b10e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b10e14 X0 X1 X2
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e49 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op y x)) x) = X0 := by
              intro X0
              first
              | (have i₁ := b10e14 X0 x x
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b10e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e54 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e48 X0 X1 X2 x
                 have i₂ := b10e53 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b10e53 b10e48
              | exact resolve b10e48 b10e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e48
            have b10e62 : (M.op y y) ≠ (M.op y y) ∨ y = (M.op x x) ∨ (M.op y y) = (k y x) := by
              first
              | (have i₁ := b10e18 y x
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e18
              | (have j0 := b10e18 y x
                 grind)
              | (have r₁ := b10e18 y x
                 have r₂ := b10e26
                 grind)
              | exact resolve b10e18 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e69 : y = (M.op x x) ∨ (M.op y y) = (k y x) := by grind
            clear b10e62
            have b10e72 : (M.op y y) = (k y x) := by
              first
              | (have r₁ := b10e69
                 have r₂ := b10e25
                 grind)
              | exact resolve b10e69 b10e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e69
            have b10e138 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op y x)))) X1) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 x (M.op (M.op x X0) (M.op y x)) X1
                 have i₂ := b10e49 X0
                 grind)
              | exact superpose b10e49 b10e14
              | exact resolve b10e14 b10e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e49
            have b10e139 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op y x)) X0) := by
              intro X0
              first
              | (have i₁ := b10e138 X0 x
                 have i₂ := b10e53 (M.op (M.op x X0) (M.op y x)) x X0
                 grind)
              | exact superpose b10e53 b10e138
              | exact resolve b10e138 b10e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e53 b10e138
            have b10e143 : x = y := by
              first
              | (have i₁ := b10e139 x
                 have i₂ := b10e54 x x y
                 grind)
              | exact superpose b10e54 b10e139
              | exact resolve b10e139 b10e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e54 b10e139
            have b10e149 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b10e28
                 have i₂ := b10e143
                 grind)
              | exact superpose b10e143 b10e28
              | exact resolve b10e28 b10e143
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e28
            have b10e152 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b10e32
                 have i₂ := b10e143
                 grind)
              | exact superpose b10e143 b10e32
              | exact resolve b10e32 b10e143
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e32
            have b10e158 : (M.op y y) = (k y y) := by
              first
              | (have i₁ := b10e72
                 have i₂ := b10e143
                 grind)
              | exact superpose b10e143 b10e72
              | exact resolve b10e72 b10e143
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e72
            have b10e159 : (σ y) = (σ (M.op y y)) := by
              first
              | (have i₁ := b10e152
                 have i₂ := b10e158
                 grind)
              | exact superpose b10e158 b10e152
              | exact resolve b10e152 b10e158
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e152 b10e158
            have b10e160 : (σ x) ≠ (σ (M.op y y)) := by
              first
              | (have i₁ := b10e149
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e149
              | exact resolve b10e149 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e149
            have b10e161 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b10e160
                 have i₂ := b10e159
                 grind)
              | exact superpose b10e159 b10e160
              | exact resolve b10e160 b10e159
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e159 b10e160
            have b10e162 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b10e161
                 have i₂ := b10e143
                 grind)
              | exact superpose b10e143 b10e161
              | exact resolve b10e161 b10e143
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e143 b10e161
            have b10e163 : False := by grind
            exact b10e163
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b11e23 : (M.op x x) = (M.op y x) := by grind
            have b11e26 : (M.op x y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b11e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b11e14 X0 X1 X2
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e47 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op y x)) x) = X0 := by
              intro X0
              first
              | (have i₁ := b11e14 X0 x x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e50 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b11e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e51 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e46 X0 X1 X2 x
                 have i₂ := b11e50 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b11e50 b11e46
              | exact resolve b11e46 b11e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e46
            have b11e124 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op y x)))) X1) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 x (M.op (M.op x X0) (M.op y x)) X1
                 have i₂ := b11e47 X0
                 grind)
              | exact superpose b11e47 b11e14
              | exact resolve b11e14 b11e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e47
            have b11e125 : ∀ X0 : G, x = (M.op (M.op (M.op x X0) (M.op y x)) X0) := by
              intro X0
              first
              | (have i₁ := b11e124 X0 x
                 have i₂ := b11e50 (M.op (M.op x X0) (M.op y x)) x X0
                 grind)
              | exact superpose b11e50 b11e124
              | exact resolve b11e124 b11e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50 b11e124
            have b11e129 : x = y := by
              first
              | (have i₁ := b11e125 x
                 have i₂ := b11e51 x x y
                 grind)
              | exact superpose b11e51 b11e125
              | exact resolve b11e125 b11e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e51 b11e125
            have b11e136 : (M.op y y) ≠ (M.op y y) := by
              first
              | (have i₁ := b11e26
                 have i₂ := b11e129
                 grind)
              | exact superpose b11e129 b11e26
              | exact resolve b11e26 b11e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e129
            have b11e144 : False := by grind
            exact b11e144
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b12e22 : x ≠ (M.op y y) := by grind
            have b12e23 : (M.op x x) = (M.op y x) := by grind
            have b12e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : y = (M.op y x) := by
              first
              | (have i₁ := b12e23
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e23
              | exact resolve b12e23 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) X0) := by
              intro X0
              first
              | (have i₁ := b12e14 x y X0
                 have i₂ := b12e28
                 grind)
              | exact superpose b12e28 b12e14
              | exact resolve b12e14 b12e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28
            have b12e42 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b12e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b12e14 b12e14
              | exact resolve b12e14 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e44 : x = (M.op y y) := by
              first
              | (have i₁ := b12e37 x
                 have i₂ := b12e42 y x y
                 grind)
              | exact superpose b12e42 b12e37
              | exact resolve b12e37 b12e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e42
            have b12e46 : False := by grind
            exact b12e46
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e23 : x ≠ (M.op y y) := by grind
              have b13e24 : (M.op x x) = (M.op y x) := by grind
              have b13e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b13e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
              have b13e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : x ≠ (M.op x y) := by
                first
                | (have i₁ := b13e23
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e23
                | exact resolve b13e23 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b13e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b13e15 X0 X1 X2
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e37 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x x)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b13e15 X0 x y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b13e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e36 X0 X1 X2 x
                   have i₂ := b13e40 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b13e40 b13e36
                | exact resolve b13e36 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e36
              have b13e53 : (M.op x x) ≠ (M.op x x) ∨ x = (M.op y y) ∨ (M.op x x) = (k x y) := by
                first
                | (have i₁ := b13e19 x y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e19
                | (have j0 := b13e19 x y
                   grind)
                | (have r₁ := b13e19 x y
                   have r₂ := b13e24
                   grind)
                | exact resolve b13e19 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b13e19 (σ x) (σ y)
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e19
                | (have j0 := b13e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b13e19 (σ x) (σ y)
                   have r₂ := b13e26
                   grind)
                | exact resolve b13e19 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e59 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
              clear b13e56
              have b13e61 : x = (M.op y y) ∨ (M.op x x) = (k x y) := by grind
              clear b13e53
              have b13e62 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b13e59
                   have r₂ := b13e25
                   grind)
                | exact resolve b13e59 b13e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e59
              have b13e63 : x = (M.op x y) ∨ (M.op x x) = (k x y) := by
                first
                | (have i₁ := b13e61
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e61
                | exact resolve b13e61 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e61
              have b13e64 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b13e62
                   have i₂ := b13e21 x y
                   grind)
                | exact superpose b13e21 b13e62
                | exact resolve b13e62 b13e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e62
              have b13e65 : (M.op x x) = (k x y) := by
                first
                | (have r₁ := b13e63
                   have r₂ := b13e30
                   grind)
                | exact resolve b13e63 b13e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30 b13e63
              have b13e146 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op x x)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 y (M.op (M.op x X0) (M.op x x)) X1
                   have i₂ := b13e37 X0
                   grind)
                | exact superpose b13e37 b13e15
                | exact resolve b13e15 b13e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37
              have b13e147 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b13e146 X0 x
                   have i₂ := b13e40 (M.op (M.op x X0) (M.op x x)) x X0
                   grind)
                | exact superpose b13e40 b13e146
                | exact resolve b13e146 b13e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e40 b13e146
              have b13e149 : x = y := by
                first
                | (have i₁ := b13e147 x
                   have i₂ := b13e41 x x x
                   grind)
                | exact superpose b13e41 b13e147
                | exact resolve b13e147 b13e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e41 b13e147
              have b13e154 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e149
                   grind)
                | exact superpose b13e149 b13e22
                | exact resolve b13e22 b13e149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e149
              have b13e163 : (σ (k x y)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b13e154
                   have i₂ := b13e64
                   grind)
                | exact superpose b13e64 b13e154
                | exact resolve b13e154 b13e64
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e64 b13e154
              have b13e165 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b13e163
                   have i₂ := b13e65
                   grind)
                | exact superpose b13e65 b13e163
                | exact resolve b13e163 b13e65
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e65 b13e163
              have b13e166 : False := by grind
              exact b13e166
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b14e24 : (M.op x x) = (M.op y x) := by grind
              have b14e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b14e15 X0 X1 X2
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e38 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x x)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b14e15 X0 x y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b14e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e37 X0 X1 X2 x
                   have i₂ := b14e40 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b14e40 b14e37
                | exact resolve b14e37 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e37
              have b14e124 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op x x)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e15 y (M.op (M.op x X0) (M.op x x)) X1
                   have i₂ := b14e38 X0
                   grind)
                | exact superpose b14e38 b14e15
                | exact resolve b14e15 b14e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e38
              have b14e125 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b14e124 X0 x
                   have i₂ := b14e40 (M.op (M.op x X0) (M.op x x)) x X0
                   grind)
                | exact superpose b14e40 b14e124
                | exact resolve b14e124 b14e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e40 b14e124
              have b14e126 : x = y := by
                first
                | (have i₁ := b14e125 x
                   have i₂ := b14e41 x x x
                   grind)
                | exact superpose b14e41 b14e125
                | exact resolve b14e125 b14e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e41 b14e125
              have b14e130 : (M.op x x) ≠ (M.op x x) := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e126
                   grind)
                | exact superpose b14e126 b14e28
                | exact resolve b14e28 b14e126
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e126
              have b14e134 : False := by grind
              exact b14e134
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b15e22 : x ≠ (M.op y y) := by grind
            have b15e23 : (M.op x x) = (M.op y x) := by grind
            have b15e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e28 : y = (M.op y x) := by
              first
              | (have i₁ := b15e23
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e23
              | exact resolve b15e23 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e37 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 y)) X0) := by
              intro X0
              first
              | (have i₁ := b15e14 x y X0
                 have i₂ := b15e28
                 grind)
              | exact superpose b15e28 b15e14
              | exact resolve b15e14 b15e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e28
            have b15e42 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b15e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b15e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b15e14 b15e14
              | exact resolve b15e14 b15e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e44 : x = (M.op y y) := by
              first
              | (have i₁ := b15e37 x
                 have i₂ := b15e42 y x y
                 grind)
              | exact superpose b15e42 b15e37
              | exact resolve b15e37 b15e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37 b15e42
            have b15e46 : False := by grind
            exact b15e46
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b16e24 : (M.op x x) = (M.op y x) := by grind
              have b16e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b16e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b16e15 X0 X1 X2
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e37 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x x)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b16e15 X0 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b16e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b16e15 b16e15
                | exact resolve b16e15 b16e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b16e36 X0 X1 X2 x
                   have i₂ := b16e40 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b16e40 b16e36
                | exact resolve b16e36 b16e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e36
              have b16e126 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op x x)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 y (M.op (M.op x X0) (M.op x x)) X1
                   have i₂ := b16e37 X0
                   grind)
                | exact superpose b16e37 b16e15
                | exact resolve b16e15 b16e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e37
              have b16e127 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b16e126 X0 x
                   have i₂ := b16e40 (M.op (M.op x X0) (M.op x x)) x X0
                   grind)
                | exact superpose b16e40 b16e126
                | exact resolve b16e126 b16e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e40 b16e126
              have b16e129 : x = y := by
                first
                | (have i₁ := b16e127 x
                   have i₂ := b16e41 x x x
                   grind)
                | exact superpose b16e41 b16e127
                | exact resolve b16e127 b16e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e41 b16e127
              have b16e136 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b16e26
                   have i₂ := b16e129
                   grind)
                | exact superpose b16e129 b16e26
                | exact resolve b16e26 b16e129
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e129
              have b16e143 : False := by grind
              exact b16e143
            · have b17e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b17e24 : (M.op x x) = (M.op y x) := by grind
              have b17e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b17e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b17e15 X0 X1 X2
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e38 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x x)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b17e15 X0 x y
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b17e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b17e15 b17e15
                | exact resolve b17e15 b17e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b17e37 X0 X1 X2 x
                   have i₂ := b17e40 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b17e40 b17e37
                | exact resolve b17e37 b17e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37
              have b17e114 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op x X0) (M.op x x)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 y (M.op (M.op x X0) (M.op x x)) X1
                   have i₂ := b17e38 X0
                   grind)
                | exact superpose b17e38 b17e15
                | exact resolve b17e15 b17e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e38
              have b17e115 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) (M.op x x)) X0) := by
                intro X0
                first
                | (have i₁ := b17e114 X0 x
                   have i₂ := b17e40 (M.op (M.op x X0) (M.op x x)) x X0
                   grind)
                | exact superpose b17e40 b17e114
                | exact resolve b17e114 b17e40
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e40 b17e114
              have b17e116 : x = y := by
                first
                | (have i₁ := b17e115 x
                   have i₂ := b17e41 x x x
                   grind)
                | exact superpose b17e41 b17e115
                | exact resolve b17e115 b17e41
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e41 b17e115
              have b17e121 : (M.op x x) ≠ (M.op x x) := by
                first
                | (have i₁ := b17e28
                   have i₂ := b17e116
                   grind)
                | exact superpose b17e116 b17e28
                | exact resolve b17e28 b17e116
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e116
              have b17e125 : False := by grind
              exact b17e125
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : x ≠ (M.op y y) := by grind
          have b18e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b18e23 : (σ x) = (M.op (σ y) (σ y)) := by grind
          have b18e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : y ≠ (M.op y x) := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e22
            | exact resolve b18e22 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e28 : (σ y) = (k (σ x) (σ y)) := by grind
          have b18e29 : (σ y) = (σ (k x y)) := by
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
          have b18e30 : (k x y) = (τ (σ y)) := by
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
          have b18e31 : y = (k x y) := by
            first
            | (have i₁ := b18e30
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e30
            | exact resolve b18e30 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e42 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
            intro X0
            first
            | (have i₁ := b18e13 x x X0
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e13
            | exact resolve b18e13 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e48 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
               have i₂ := b18e13 X0 X1 (M.op X2 (M.op X1 X0))
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e51 : x = (M.op x y) := by
            first
            | (have i₁ := b18e42 x
               have i₂ := b18e48 x x y
               grind)
            | exact superpose b18e48 b18e42
            | exact resolve b18e42 b18e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42 b18e48
          have b18e97 : y = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
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
          have b18e105 : y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have r₁ := b18e97
               have r₂ := b18e21
               grind)
            | exact resolve b18e97 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e97
          have b18e113 : x = y ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b18e105
               have i₂ := b18e51
               grind)
            | exact superpose b18e51 b18e105
            | exact resolve b18e105 b18e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e105
          have b18e116 : y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b18e113
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e113
            | exact resolve b18e113 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e113
          have b18e119 : x = y := by
            first
            | (have r₁ := b18e116
               have r₂ := b18e26
               grind)
            | exact resolve b18e116 b18e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e116
          have b18e124 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b18e26
               have i₂ := b18e119
               grind)
            | exact superpose b18e119 b18e26
            | exact resolve b18e26 b18e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e26
          have b18e129 : x = (M.op x x) := by
            first
            | (have i₁ := b18e51
               have i₂ := b18e119
               grind)
            | exact superpose b18e119 b18e51
            | exact resolve b18e51 b18e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e51 b18e119
          have b18e130 : False := by grind
          exact b18e130
        · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : x ≠ (M.op y y) := by grind
            have b19e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b19e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b19e26 : (M.op x y) = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e29 : (σ y) = (k (σ x) (σ y)) := by grind
            have b19e30 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b19e29
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e29
              | exact resolve b19e29 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e31 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e30
                 grind)
              | exact superpose b19e30 b19e15
              | exact resolve b19e15 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : y = (k x y) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e31
              | exact resolve b19e31 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e45 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b19e14 X0 X1 X2
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e46 : ∀ X0 : G, (M.op (M.op (M.op y X0) (M.op y y)) x) = X0 := by
              intro X0
              first
              | (have i₁ := b19e14 X0 y x
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e49 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b19e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e50 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e45 X0 X1 X2 x
                 have i₂ := b19e49 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b19e49 b19e45
              | exact resolve b19e45 b19e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e45
            have b19e94 : y = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b19e32
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e32
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e32 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e102 : y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b19e94
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e94 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e94
            have b19e110 : y = (M.op x y) := by
              first
              | (have r₁ := b19e102
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e102 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e102
            have b19e114 : y = (M.op y y) := by
              first
              | (have i₁ := b19e26
                 have i₂ := b19e110
                 grind)
              | exact superpose b19e110 b19e26
              | exact resolve b19e26 b19e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e110
            have b19e123 : x ≠ y := by
              first
              | (have i₁ := b19e22
                 have i₂ := b19e114
                 grind)
              | exact superpose b19e114 b19e22
              | exact resolve b19e22 b19e114
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e114
            have b19e147 : ∀ X0 X1 : G, x = (M.op (M.op X0 (M.op X1 (M.op (M.op y X0) (M.op y y)))) X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 x (M.op (M.op y X0) (M.op y y)) X1
                 have i₂ := b19e46 X0
                 grind)
              | exact superpose b19e46 b19e14
              | exact resolve b19e14 b19e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e46
            have b19e148 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) (M.op y y)) X0) := by
              intro X0
              first
              | (have i₁ := b19e147 X0 x
                 have i₂ := b19e49 (M.op (M.op y X0) (M.op y y)) x X0
                 grind)
              | exact superpose b19e49 b19e147
              | exact resolve b19e147 b19e49
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e49 b19e147
            have b19e155 : x = y := by
              first
              | (have i₁ := b19e148 x
                 have i₂ := b19e50 x y y
                 grind)
              | exact superpose b19e50 b19e148
              | exact resolve b19e148 b19e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e50 b19e148
            have b19e160 : False := by grind
            exact b19e160
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b20e22 : x ≠ (M.op y y) := by grind
            have b20e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b20e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b20e26 : (M.op x y) ≠ (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ y) = (k (σ x) (σ y)) := by grind
            have b20e29 : (σ y) = (σ (k x y)) := by
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
            have b20e30 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e29
                 grind)
              | exact superpose b20e29 b20e15
              | exact resolve b20e15 b20e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e31 : y = (k x y) := by
              first
              | (have i₁ := b20e30
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e30
              | exact resolve b20e30 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e52 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by
              first
              | (have i₁ := b20e18 (σ y) (σ y)
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e18
              | exact resolve b20e18 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e56 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) := by grind
            clear b20e52
            have b20e57 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e56
                 have i₂ := b20e20 y y
                 grind)
              | exact superpose b20e20 b20e56
              | exact resolve b20e56 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e56
            have b20e83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have i₁ := b20e18 X0 X1
                 have i₂ := b20e19 X0 X1
                 grind)
              | (have i₁ := b20e18 X0 X0
                 have i₂ := b20e19 X0 X1
                 grind)
              | exact superpose b20e19 b20e18
              | (have j0 := b20e18 X0 X1
                 have j1 := b20e19 X0 X1
                 grind)
              | (have r₁ := b20e18 X1 X1
                 have r₂ := b20e19 (M.op X1 X1) X1
                 grind)
              | (have r₁ := b20e18 X1 X1
                 have r₂ := b20e19 (M.op X1 X1) X1
                 grind)
              | (have r₁ := b20e18 X0 X1
                 have r₂ := b20e19 X0 X1
                 grind)
              | exact resolve b20e18 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e97 : y = (M.op x y) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
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
            have b20e98 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e29
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e29 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e100 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b20e83 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e83
            have b20e101 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b20e100 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e100
            have b20e103 : (σ (M.op x y)) = (σ y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b20e98
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e98 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e98
            have b20e104 : y = (M.op x y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b20e97
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e97 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e97
            have b20e111 : (σ (M.op x y)) = (σ y) := by
              first
              | (have r₁ := b20e103
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e103 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e103
            have b20e112 : y = (M.op x y) := by
              first
              | (have r₁ := b20e104
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e104 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e104
            have b20e114 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b20e26
                 have i₂ := b20e112
                 grind)
              | exact superpose b20e112 b20e26
              | exact resolve b20e26 b20e112
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e112
            have b20e273 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e15 (k y y)
                 have i₂ := b20e57
                 grind)
              | exact superpose b20e57 b20e15
              | exact resolve b20e15 b20e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e57
            have b20e274 : x = (k y y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e273
                 have i₂ := b20e15 x
                 grind)
              | exact superpose b20e15 b20e273
              | exact resolve b20e273 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e273
            have b20e1194 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b20e101 y y
                 have i₂ := b20e274
                 grind)
              | exact superpose b20e274 b20e101
              | (have j0 := b20e101 x y
                 grind)
              | exact resolve b20e101 b20e274
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e101 b20e274
            have b20e1195 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
            clear b20e1194
            have b20e1197 : y = (M.op y y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b20e1195
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e1195 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1195
            have b20e1201 : (σ x) = (σ y) := by
              first
              | (have r₁ := b20e1197
                 have r₂ := b20e114
                 grind)
              | exact resolve b20e1197 b20e114
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e114 b20e1197
            have b20e1244 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b20e21
                 have i₂ := b20e1201
                 grind)
              | exact superpose b20e1201 b20e21
              | exact resolve b20e21 b20e1201
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e1255 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b20e1244
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e1244
              | exact resolve b20e1244 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1244
            have b20e1257 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b20e1255
                 have i₂ := b20e1201
                 grind)
              | exact superpose b20e1201 b20e1255
              | exact resolve b20e1255 b20e1201
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e1201 b20e1255
            have b20e1259 : False := by grind
            exact b20e1259
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b21e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b21e25 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
            have b21e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e28 : y ≠ (M.op y x) := by
              first
              | (have i₁ := b21e23
                 have i₂ := b21e26
                 grind)
              | exact superpose b21e26 b21e23
              | exact resolve b21e23 b21e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e36 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
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
            have b21e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b21e14 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                 have i₂ := b21e14 X0 X1 X2
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b21e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b21e14 b21e14
              | exact resolve b21e14 b21e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b21e37 X0 X1 X2 x
                 have i₂ := b21e40 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                 grind)
              | exact superpose b21e40 b21e37
              | exact resolve b21e37 b21e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e37
            have b21e42 : x = (M.op x y) := by
              first
              | (have i₁ := b21e36 x
                 have i₂ := b21e40 x x y
                 grind)
              | exact superpose b21e40 b21e36
              | exact resolve b21e36 b21e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e36 b21e40
            have b21e233 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ x))) X0) := by
              intro X0
              first
              | (have i₁ := b21e41 X0 (σ x) (σ y)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e41
              | exact resolve b21e41 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e255 : (σ x) = (σ y) := by
              first
              | (have i₁ := b21e233 x
                 have i₂ := b21e41 x (σ x) (σ x)
                 grind)
              | exact superpose b21e41 b21e233
              | exact resolve b21e233 b21e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e41 b21e233
            have b21e285 : y = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 y
                 have i₂ := b21e255
                 grind)
              | exact superpose b21e255 b21e15
              | exact resolve b21e15 b21e255
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e255
            have b21e286 : x = y := by
              first
              | (have i₁ := b21e285
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e285
              | exact resolve b21e285 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e285
            have b21e325 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b21e28
                 have i₂ := b21e286
                 grind)
              | exact superpose b21e286 b21e28
              | exact resolve b21e28 b21e286
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e28
            have b21e328 : x = (M.op x x) := by
              first
              | (have i₁ := b21e42
                 have i₂ := b21e286
                 grind)
              | exact superpose b21e286 b21e42
              | exact resolve b21e42 b21e286
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e42 b21e286
            have b21e337 : False := by grind
            exact b21e337
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b22e24 : (M.op x x) ≠ (M.op y x) := by grind
              have b22e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b22e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b22e15 X0 X1 X2
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e36 : ∀ X0 : G, (M.op (M.op (M.op y X0) (M.op x y)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b22e15 X0 y y
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e38 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b22e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b22e15 b22e15
                | exact resolve b22e15 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e35 X0 X1 X2 x
                   have i₂ := b22e38 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b22e38 b22e35
                | exact resolve b22e35 b22e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e35
              have b22e123 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op y X0) (M.op x y)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b22e15 y (M.op (M.op y X0) (M.op x y)) X1
                   have i₂ := b22e36 X0
                   grind)
                | exact superpose b22e36 b22e15
                | exact resolve b22e15 b22e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e36
              have b22e124 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) (M.op x y)) X0) := by
                intro X0
                first
                | (have i₁ := b22e123 X0 x
                   have i₂ := b22e38 (M.op (M.op y X0) (M.op x y)) x X0
                   grind)
                | exact superpose b22e38 b22e123
                | exact resolve b22e123 b22e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e38 b22e123
              have b22e128 : x = y := by
                first
                | (have i₁ := b22e124 x
                   have i₂ := b22e39 x y x
                   grind)
                | exact superpose b22e39 b22e124
                | exact resolve b22e124 b22e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39 b22e124
              have b22e134 : (M.op x x) ≠ (M.op x x) := by
                first
                | (have i₁ := b22e24
                   have i₂ := b22e128
                   grind)
                | exact superpose b22e128 b22e24
                | exact resolve b22e24 b22e128
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e128
              have b22e140 : False := by grind
              exact b22e140
            · have b23e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e26 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
              have b23e28 : (M.op x y) ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b23e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b23e15 X0 X1 X2
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e38 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b23e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b23e15 b23e15
                | exact resolve b23e15 b23e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b23e36 X0 X1 X2 x
                   have i₂ := b23e38 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b23e38 b23e36
                | exact resolve b23e36 b23e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36 b23e38
              have b23e176 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ x))) X0) := by
                intro X0
                first
                | (have i₁ := b23e39 X0 (σ x) (σ y)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e39
                | exact resolve b23e39 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e204 : (σ x) = (σ y) := by
                first
                | (have i₁ := b23e176 x
                   have i₂ := b23e39 x (σ x) (σ x)
                   grind)
                | exact superpose b23e39 b23e176
                | exact resolve b23e176 b23e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e39 b23e176
              have b23e223 : y = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 y
                   have i₂ := b23e204
                   grind)
                | exact superpose b23e204 b23e16
                | exact resolve b23e16 b23e204
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e204
              have b23e224 : x = y := by
                first
                | (have i₁ := b23e223
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e223
                | exact resolve b23e223 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e223
              have b23e263 : (M.op x x) ≠ (M.op x x) := by
                first
                | (have i₁ := b23e28
                   have i₂ := b23e224
                   grind)
                | exact superpose b23e224 b23e28
                | exact resolve b23e28 b23e224
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e224
              have b23e266 : False := by grind
              exact b23e266
        · rcases eq_or_ne (M.op x x) (y) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
              intro X0 X1 X2
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : x ≠ (M.op y y) := by grind
            have b24e23 : (M.op x x) ≠ (M.op y x) := by grind
            have b24e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b24e25 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : y ≠ (M.op y x) := by
              first
              | (have i₁ := b24e23
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e23
              | exact resolve b24e23 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : ∀ X0 : G, x = (M.op (M.op y (M.op X0 x)) X0) := by
              intro X0
              first
              | (have i₁ := b24e14 x x X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e40 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                 have i₂ := b24e14 X0 X1 (M.op X2 (M.op X1 X0))
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e42 : x = (M.op x y) := by
              first
              | (have i₁ := b24e36 x
                 have i₂ := b24e40 x x y
                 grind)
              | exact superpose b24e40 b24e36
              | exact resolve b24e36 b24e40
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36 b24e40
            have b24e78 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b24e24
                 have i₂ := b24e19 X0 (σ y)
                 grind)
              | (have i₁ := b24e24
                 have i₂ := b24e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b24e19 b24e24
              | (have j1 := b24e19 X0 (σ y)
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e19 (σ x) (σ y)
                 grind)
              | exact resolve b24e24 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e1346 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have j0 := b24e78 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e78
            have b24e1347 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b24e1346
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e1346 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1346
            have b24e1348 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b24e1347
                 have i₂ := b24e20 x y
                 grind)
              | exact superpose b24e20 b24e1347
              | exact resolve b24e1347 b24e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1347
            have b24e1349 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1348
                 grind)
              | exact superpose b24e1348 b24e21
              | exact resolve b24e21 b24e1348
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1348
            have b24e1366 : (σ x) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e1349
                 have i₂ := b24e42
                 grind)
              | exact superpose b24e42 b24e1349
              | exact resolve b24e1349 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1349
            have b24e1389 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b24e1366
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1366
              | (have j1 := b24e19 x y
                 grind)
              | exact resolve b24e1366 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1366
            have b24e1390 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have r₁ := b24e1389
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e1389 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1389
            have b24e1395 : (σ x) ≠ (σ x) ∨ (M.op x x) = (M.op y x) := by
              first
              | (have i₁ := b24e1390
                 have i₂ := b24e42
                 grind)
              | exact superpose b24e42 b24e1390
              | exact resolve b24e1390 b24e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e42 b24e1390
            have b24e1396 : (M.op x x) = (M.op y x) := by grind
            clear b24e1395
            have b24e1402 : y = (M.op y x) := by
              first
              | (have i₁ := b24e1396
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e1396
              | exact resolve b24e1396 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1396
            have b24e1406 : False := by grind
            exact b24e1406
          · rcases eq_or_ne (M.op y y) (M.op x y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b25e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e28 : (M.op x y) = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 (M.op (M.op X1 X0) (M.op X2 X1)))) X3) = X2 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X1 X0) (M.op X2 X1)) X3
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 : G, (M.op (M.op (M.op y X0) (M.op x y)) y) = X0 := by
                intro X0
                first
                | (have i₁ := b25e15 X0 y y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b25e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e35 X0 X1 X2 x
                   have i₂ := b25e38 (M.op (M.op X1 X0) (M.op X2 X1)) x X0
                   grind)
                | exact superpose b25e38 b25e35
                | exact resolve b25e35 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35
              have b25e114 : ∀ X0 X1 : G, y = (M.op (M.op X0 (M.op X1 (M.op (M.op y X0) (M.op x y)))) X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 y (M.op (M.op y X0) (M.op x y)) X1
                   have i₂ := b25e36 X0
                   grind)
                | exact superpose b25e36 b25e15
                | exact resolve b25e15 b25e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36
              have b25e115 : ∀ X0 : G, y = (M.op (M.op (M.op y X0) (M.op x y)) X0) := by
                intro X0
                first
                | (have i₁ := b25e114 X0 x
                   have i₂ := b25e38 (M.op (M.op y X0) (M.op x y)) x X0
                   grind)
                | exact superpose b25e38 b25e114
                | exact resolve b25e114 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38 b25e114
              have b25e119 : x = y := by
                first
                | (have i₁ := b25e115 x
                   have i₂ := b25e39 x y x
                   grind)
                | exact superpose b25e39 b25e115
                | exact resolve b25e115 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e115
              have b25e127 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b25e26
                   have i₂ := b25e119
                   grind)
                | exact superpose b25e119 b25e26
                | exact resolve b25e26 b25e119
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e119
              have b25e132 : False := by grind
              exact b25e132
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X1)) X2) = X0 := by
                intro X0 X1 X2
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e23 : x ≠ (M.op y y) := by grind
              have b26e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b26e26 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e38 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) X1) = (M.op X0 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 (M.op (M.op X2 (M.op X1 X0)) X1) (M.op X1 X0) X2
                   have i₂ := b26e15 X0 X1 (M.op X2 (M.op X1 X0))
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e85 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b26e25
                   have i₂ := b26e20 X0 (σ y)
                   grind)
                | (have i₁ := b26e25
                   have i₂ := b26e20 (M.op (σ y) (σ y)) x
                   grind)
                | exact superpose b26e20 b26e25
                | (have j1 := b26e20 X0 (σ y)
                   grind)
                | (have r₁ := b26e25
                   have r₂ := b26e20 (σ x) (σ y)
                   grind)
                | exact resolve b26e25 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e86 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e19 X0 X1
                   have i₂ := b26e20 X0 X1
                   grind)
                | (have i₁ := b26e19 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e19
                | (have j0 := b26e19 X0 X1
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 (M.op X1 X1) X1
                   grind)
                | (have r₁ := b26e19 X1 X1
                   have r₂ := b26e20 (M.op X1 X1) X1
                   grind)
                | (have r₁ := b26e19 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | exact resolve b26e19 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e94 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X2 X1)) X2) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X1 X1 X2
                   have i₂ := b26e20 X1 X0
                   grind)
                | (have i₁ := b26e15 X0 X1 X2
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e15
                | (have j1 := b26e20 X1 X0
                   grind)
                | exact resolve b26e15 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e86 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e86
              have b26e104 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e103 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e103
              have b26e107 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e94 X0 X1 x
                   have i₂ := b26e38 X1 x (M.op X0 X1)
                   grind)
                | exact superpose b26e38 b26e94
                | (have j0 := b26e94 X0 X1 x
                   grind)
                | exact resolve b26e94 b26e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e94
              have b26e894 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e104 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e104
              have b26e982 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e38 X0 X1 X0
                   have i₂ := b26e107 X1 X0
                   grind)
                | exact superpose b26e107 b26e38
                | (have j1 := b26e107 X1 X0
                   grind)
                | exact resolve b26e38 b26e107
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38 b26e107
              have b26e1057 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e982 X0 X1
                   have j1 := b26e894 X0 X1
                   grind)
                | (have r₁ := b26e982 X0 X1
                   have r₂ := b26e894 X0 X1
                   grind)
                | (have r₁ := b26e982 X1 X1
                   have r₂ := b26e894 X1 X1
                   grind)
                | (have r₁ := b26e982 (M.op X0 X1) X0
                   have r₂ := b26e894 X0 X1
                   grind)
                | exact resolve b26e982 b26e894
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e894 b26e982
              have b26e1413 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have j0 := b26e85 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e85
              have b26e1414 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b26e1413
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e1413 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1413
              have b26e1415 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b26e1414
                   have i₂ := b26e21 x y
                   grind)
                | exact superpose b26e21 b26e1414
                | exact resolve b26e1414 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1414
              have b26e1416 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e1415
                   grind)
                | exact superpose b26e1415 b26e22
                | exact resolve b26e22 b26e1415
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1415
              have b26e1465 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
                first
                | (have i₁ := b26e1416
                   have i₂ := b26e1057 x y
                   grind)
                | exact superpose b26e1057 b26e1416
                | (have j1 := b26e1057 x y
                   grind)
                | exact resolve b26e1416 b26e1057
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1057 b26e1416
              have b26e1468 : x = (M.op y y) := by grind
              clear b26e1465
              have b26e1473 : False := by grind
              exact b26e1473

/-- `Equation2887`: `x = ((x ◇ (y ◇ z)) ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pxy_x_pyx_Equation2887 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2887 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2887.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x x) = (M.op y y) := by grind
      have b0e20 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e42 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 X0 x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e14 X0 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 X0 (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e194 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e42 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e369 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e43 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e371 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e369
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e369
        | exact resolve b0e369 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e369
      have b0e379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e371
           have i₂ := b0e194
           grind)
        | exact superpose b0e194 b0e371
        | exact resolve b0e371 b0e194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e194 b0e371
      have b0e382 : False := by grind
      exact b0e382
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y y) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e39 (σ X0)
             grind)
          | exact superpose b1e39 b1e18
          | exact resolve b1e18 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e41 X0
             have i₂ := b1e39 X0
             grind)
          | exact superpose b1e39 b1e41
          | exact resolve b1e41 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e41
        have b1e152 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e22
          | exact resolve b1e22 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e153 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e44 y
             grind)
          | exact superpose b1e44 b1e24
          | exact resolve b1e24 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e44
        have b1e161 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e153
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e153
          | exact resolve b1e153 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e153
        have b1e165 : False := by grind
        exact b1e165
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e51 X0
             grind)
          | exact superpose b2e51 b2e53
          | exact resolve b2e53 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e53
        have b2e144 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e60 y
             grind)
          | exact superpose b2e60 b2e21
          | exact resolve b2e21 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e152 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e144
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e144
          | exact resolve b2e144 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e144
        have b2e155 : False := by grind
        exact b2e155
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e49 (σ X0)
             grind)
          | exact superpose b3e49 b3e18
          | exact resolve b3e18 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e51 X0
             have i₂ := b3e49 X0
             grind)
          | exact superpose b3e49 b3e51
          | exact resolve b3e51 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e62 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by grind
        have b3e67 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e56 x
             grind)
          | exact superpose b3e56 b3e62
          | exact resolve b3e62 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e62
        have b3e69 : (σ (M.op x x)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e67
             have i₂ := b3e56 (M.op x x)
             grind)
          | exact superpose b3e56 b3e67
          | exact resolve b3e67 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e67
        have b3e70 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (k (σ y) (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b3e69
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e69
          | exact resolve b3e69 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e71 : (σ y) = (k (σ y) (σ (M.op x x))) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e70
             have i₂ := b3e56 x
             grind)
          | exact superpose b3e56 b3e70
          | exact resolve b3e70 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e70
        have b3e72 : (σ y) = (σ (k y (M.op x x))) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e71
             have i₂ := b3e18 y (M.op x x)
             grind)
          | exact superpose b3e18 b3e71
          | exact resolve b3e71 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e73 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e72
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e72
          | exact resolve b3e72 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e74 : (σ y) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e73
             have i₂ := b3e49 y
             grind)
          | exact superpose b3e49 b3e73
          | exact resolve b3e73 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49 b3e73
        have b3e75 : (σ y) = (σ (M.op y y)) := by grind
        clear b3e74
        have b3e141 : (M.op y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (M.op y y)
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e13
          | exact resolve b3e13 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e142 : y = (M.op y y) := by
          first
          | (have i₁ := b3e141
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e141
          | exact resolve b3e141 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e141
        have b3e145 : False := by grind
        exact b3e145
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e23
            | exact resolve b4e23 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ x)) (σ x)) = X0 := by
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
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
               have i₂ := b4e13 X0 (M.op X1 X2) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e44 (σ X0)
               grind)
            | exact superpose b4e44 b4e19
            | exact resolve b4e19 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e46 X0
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e46
            | exact resolve b4e46 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e46
          have b4e74 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (σ X0) (σ X1)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e87 : ∀ X0 : G, (M.op X0 X0) ≠ y ∨ (M.op X0 y) = (k y X0) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e27
               have i₂ := b4e18 y X0
               grind)
            | (have i₁ := b4e27
               have i₂ := b4e18 X0 y
               grind)
            | exact superpose b4e18 b4e27
            | (have j1 := b4e18 y X0
               grind)
            | (have r₁ := b4e27
               have r₂ := b4e18 y y
               grind)
            | exact resolve b4e27 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e105 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e74 X0 X1
               have i₂ := b4e49 X1
               grind)
            | exact superpose b4e49 b4e74
            | (have j0 := b4e74 X0 X1
               grind)
            | exact resolve b4e74 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e107 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e105 X0 X1
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e105
            | (have j0 := b4e105 X0 X1
               grind)
            | exact resolve b4e105 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e109 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e107 X0 X1
               have i₂ := b4e49 X1
               grind)
            | exact superpose b4e49 b4e107
            | (have j0 := b4e107 X0 X1
               grind)
            | exact resolve b4e107 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e107
          have b4e156 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e49 y
               grind)
            | exact superpose b4e49 b4e26
            | exact resolve b4e26 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e157 : (σ y) = (M.op (M.op (σ (M.op y y)) (σ x)) (σ x)) := by
            first
            | (have i₁ := b4e35 (σ y)
               have i₂ := b4e49 y
               grind)
            | exact superpose b4e49 b4e35
            | exact resolve b4e35 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e308 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 (M.op X1 X2) x
               have i₂ := b4e37 X0 X1 X2 x
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e350 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e87 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e87
            | (have j0 := b4e87 x
               grind)
            | (have r₁ := b4e87 x
               have r₂ := b4e22
               grind)
            | exact resolve b4e87 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e87
          have b4e351 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by grind
          clear b4e350
          have b4e362 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (σ x)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b4e308 (σ x) (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e308
            | exact resolve b4e308 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e367 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e308 (M.op X0 (σ y)) (σ x) X1
               have i₂ := b4e35 X0
               grind)
            | exact superpose b4e35 b4e308
            | exact resolve b4e308 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e378 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e308 X0 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e308
            | exact resolve b4e308 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e308
          have b4e394 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b4e362 x
               have i₂ := b4e367 (M.op (σ y) (σ x)) x
               grind)
            | exact superpose b4e367 b4e362
            | exact resolve b4e362 b4e367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e362 b4e367
          have b4e3088 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e109 x y
               grind)
            | exact superpose b4e109 b4e20
            | (have j1 := b4e109 y x
               grind)
            | exact resolve b4e20 b4e109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e3143 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e3088
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e3088
            | exact resolve b4e3088 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3088
          have b4e3161 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e3143
               have r₂ := b4e156
               grind)
            | exact resolve b4e3143 b4e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3143
          have b4e3446 : (M.op (σ (M.op y y)) (σ x)) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
            first
            | (have i₁ := b4e378 (M.op (σ (M.op y y)) (σ x))
               have i₂ := b4e157
               grind)
            | exact superpose b4e157 b4e378
            | exact resolve b4e378 b4e157
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e157 b4e378
          have b4e3468 : (σ x) = (M.op (σ (M.op y y)) (σ x)) := by
            first
            | (have i₁ := b4e3446
               have i₂ := b4e394
               grind)
            | exact superpose b4e394 b4e3446
            | exact resolve b4e3446 b4e394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394 b4e3446
          have b4e14630 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e3161
               have i₂ := b4e351
               grind)
            | exact superpose b4e351 b4e3161
            | exact resolve b4e3161 b4e351
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e351 b4e3161
          have b4e14651 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
          clear b4e14630
          have b4e14683 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e14651
               grind)
            | exact superpose b4e14651 b4e14
            | exact resolve b4e14 b4e14651
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14651
          have b4e14716 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e14683
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e14683
            | exact resolve b4e14683 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14683
          have b4e14717 : x = (M.op y y) := by grind
          clear b4e14716
          have b4e15679 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b4e156
               have i₂ := b4e14717
               grind)
            | exact superpose b4e14717 b4e156
            | exact resolve b4e156 b4e14717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e156
          have b4e15683 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e3468
               have i₂ := b4e14717
               grind)
            | exact superpose b4e14717 b4e3468
            | exact resolve b4e3468 b4e14717
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3468 b4e14717
          have b4e15801 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e15683
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e15683
            | exact resolve b4e15683 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e15683
          have b4e15836 : (σ x) = (σ y) := by
            first
            | (have i₁ := b4e15801
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e15801
            | exact resolve b4e15801 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e15801
          have b4e15848 : False := by grind
          exact b4e15848
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b5e45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
          have b5e150 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e45 x
               grind)
            | exact superpose b5e45 b5e24
            | exact resolve b5e24 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e162 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e150
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e150
            | exact resolve b5e150 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e150
          have b5e163 : False := by grind
          exact b5e163
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e51 (σ X0)
             grind)
          | exact superpose b6e51 b6e18
          | exact resolve b6e18 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e53 X0
             have i₂ := b6e51 X0
             grind)
          | exact superpose b6e51 b6e53
          | exact resolve b6e53 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e53
        have b6e149 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e60 y
             grind)
          | exact superpose b6e60 b6e22
          | exact resolve b6e22 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e157 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e149
             have i₂ := b6e60 x
             grind)
          | exact superpose b6e60 b6e149
          | exact resolve b6e149 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e149
        have b6e193 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e157
             grind)
          | exact superpose b6e157 b6e13
          | exact resolve b6e13 b6e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e157
        have b6e194 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e193
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e193
          | exact resolve b6e193 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e193
        have b6e200 : False := by grind
        exact b6e200
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e44 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e16 (σ x) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | (have j0 := b7e16 (σ x) X0
               grind)
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e132 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e44 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e44
            | (have r₁ := b7e44 (σ x)
               have r₂ := b7e24
               grind)
            | exact resolve b7e44 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e133 : (σ y) = (k (σ x) (σ x)) := by grind
          clear b7e132
          have b7e134 : (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e133
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e133
            | exact resolve b7e133 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e133
          have b7e135 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e134
               have i₂ := b7e46 x
               grind)
            | exact superpose b7e46 b7e134
            | exact resolve b7e134 b7e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46 b7e134
          have b7e153 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e135
               grind)
            | exact superpose b7e135 b7e14
            | exact resolve b7e14 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135
          have b7e154 : y = (M.op x x) := by
            first
            | (have i₁ := b7e153
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e153
            | exact resolve b7e153 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153
          have b7e157 : False := by grind
          exact b7e157
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) X1) X1) = X0 := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b8e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X2)) (M.op (M.op X0 (M.op X2 X3)) X2)) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op (M.op X0 (M.op X2 X3)) X2) X2
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2)) X1 X2
               have i₂ := b8e13 X0 (M.op X1 X2) X3
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e44 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e42 (σ X0)
               grind)
            | exact superpose b8e42 b8e19
            | exact resolve b8e19 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e46 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e27 X0 (τ X0)
               have i₂ := b8e42 (τ X0)
               grind)
            | exact superpose b8e42 b8e27
            | exact resolve b8e27 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e47 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e46 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e46
            | exact resolve b8e46 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e49 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e44 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e44
            | exact resolve b8e44 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e51 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e47 X0
               have i₂ := b8e42 X0
               grind)
            | exact superpose b8e42 b8e47
            | exact resolve b8e47 b8e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42 b8e47
          have b8e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
          have b8e90 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e21
               have i₂ := b8e18 y X0
               grind)
            | (have i₁ := b8e21
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e21
            | (have j1 := b8e18 y X0
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 x (M.op y y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e108 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e77
            | (have j0 := b8e77 X0 X1
               grind)
            | exact resolve b8e77 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e111 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e108 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e108
            | (have j0 := b8e108 X0 X1
               grind)
            | exact resolve b8e108 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e113 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e111 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e111
            | (have j0 := b8e111 X0 X1
               grind)
            | exact resolve b8e111 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111
          have b8e134 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X2)) = (M.op (M.op X1 (M.op X0 (M.op X2 X3))) (M.op X0 (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 X1 (M.op X0 (M.op X2 X3)) X2 X2
               have i₂ := b8e13 X0 X2 X3
               grind)
            | exact superpose b8e13 b8e29
            | exact resolve b8e29 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e146 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op (M.op (M.op X0 X1) X1) X5)) (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e29 X0 (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X2) X3
               have i₂ := b8e29 X0 X1 X2 X3
               grind)
            | exact superpose b8e29 b8e29
            | exact resolve b8e29 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e149 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X1) (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X0 (M.op X1 X2) x
               have i₂ := b8e29 X0 X1 X2 x
               grind)
            | exact superpose b8e29 b8e13
            | exact resolve b8e13 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e150 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op (M.op X0 X1) X1) X1) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2
               have i₂ := b8e29 X0 X1 X2 X3
               grind)
            | exact superpose b8e29 b8e13
            | exact resolve b8e13 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e154 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 (M.op (M.op X1 X3) X4))) (M.op X0 (M.op (M.op X1 X3) X4))) = (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e146 X0 X1 X2 X3 X4 x
               have i₂ := b8e29 X2 (M.op X0 X1) X1 x
               grind)
            | exact superpose b8e29 b8e146
            | exact resolve b8e146 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146
          have b8e158 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 (M.op (M.op X1 X3) X4)) (M.op X1 X3))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e154 X0 X1 X2 X3 X4
               have i₂ := b8e134 X0 X2 (M.op X1 X3) X4
               grind)
            | exact superpose b8e134 b8e154
            | exact resolve b8e154 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134 b8e154
          have b8e159 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e158 X0 X1 X2 x x
               have i₂ := b8e29 X0 X1 x x
               grind)
            | exact superpose b8e29 b8e158
            | exact resolve b8e158 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e158
          have b8e166 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e23
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e168 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) (σ X0)) (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e13
            | exact resolve b8e13 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e175 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e166
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e166
            | exact resolve b8e166 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e166
          have b8e205 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e51 X0
               grind)
            | exact superpose b8e51 b8e14
            | exact resolve b8e14 b8e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e261 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
            first
            | (have j0 := b8e90 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e269 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ (M.op X0 X0))) (τ X0)) (τ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (τ X0) (τ X0)
               have i₂ := b8e205 X0
               grind)
            | exact superpose b8e205 b8e13
            | exact resolve b8e13 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e312 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X2 (σ (M.op X0 X0))) (σ X0))) (M.op (M.op X2 (σ (M.op X0 X0))) (σ X0))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 X0 X1 (σ X0) (σ X0)
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e28
            | exact resolve b8e28 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e313 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op (M.op X2 (τ (M.op X0 X0))) (τ X0))) (M.op (M.op X2 (τ (M.op X0 X0))) (τ X0))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e28 X0 X1 (τ X0) (τ X0)
               have i₂ := b8e205 X0
               grind)
            | exact superpose b8e205 b8e28
            | exact resolve b8e28 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e324 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X2 X3))) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2)) X1) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e29 (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2)) X1 (M.op X2 X3) X2
               have i₂ := b8e28 X1 X0 X2 X3
               grind)
            | exact superpose b8e28 b8e29
            | exact resolve b8e29 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e339 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X2 (τ (M.op X0 X0)))) (M.op (M.op (M.op X2 (τ (M.op X0 X0))) (τ X0)) (τ X0))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e313 X0 X1 X2
               have i₂ := b8e159 (M.op X2 (τ (M.op X0 X0))) (τ X0) (M.op X1 X2)
               grind)
            | exact superpose b8e159 b8e313
            | exact resolve b8e313 b8e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e313
          have b8e340 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X2 (σ (M.op X0 X0)))) (M.op (M.op (M.op X2 (σ (M.op X0 X0))) (σ X0)) (σ X0))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e312 X0 X1 X2
               have i₂ := b8e159 (M.op X2 (σ (M.op X0 X0))) (σ X0) (M.op X1 X2)
               grind)
            | exact superpose b8e159 b8e312
            | exact resolve b8e312 b8e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e312
          have b8e361 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X2 (τ (M.op X0 X0)))) X2) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e339 X0 X1 X2
               have i₂ := b8e269 X0 X2
               grind)
            | exact superpose b8e269 b8e339
            | exact resolve b8e339 b8e269
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e269 b8e339
          have b8e362 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X2 (σ (M.op X0 X0)))) X2) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e340 X0 X1 X2
               have i₂ := b8e168 X0 X2
               grind)
            | exact superpose b8e168 b8e340
            | exact resolve b8e340 b8e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e340
          have b8e384 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) X1) = (M.op (M.op X0 X1) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e149 (M.op (M.op X0 (M.op X1 X2)) X1) X1 X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e149
            | exact resolve b8e149 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e387 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2)) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X2)) (M.op (M.op (M.op X1 (M.op X2 X3)) X2) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e149 (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2)) (M.op (M.op X1 (M.op X2 X3)) X2) X4
               have i₂ := b8e28 X1 X0 X2 X3
               grind)
            | exact superpose b8e28 b8e149
            | exact resolve b8e149 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e390 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) (σ X0)) (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e149 (σ X0) (σ X0) X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e149
            | exact resolve b8e149 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e392 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e149 (M.op X0 (M.op X1 X3)) X1 X2
               have i₂ := b8e13 X0 X1 X3
               grind)
            | exact superpose b8e13 b8e149
            | exact resolve b8e149 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e394 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 (M.op X2 X3)) X2) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e149 (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2) X4
               have i₂ := b8e28 X1 X0 X2 X3
               grind)
            | exact superpose b8e28 b8e149
            | exact resolve b8e149 b8e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28
          have b8e403 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ X0)) (σ X0)) (σ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e149 X1 (σ X0) (σ X0)
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e149
            | exact resolve b8e149 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e404 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (τ X0)) (τ X0)) (τ (M.op X0 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e149 X1 (τ X0) (τ X0)
               have i₂ := b8e205 X0
               grind)
            | exact superpose b8e205 b8e149
            | exact resolve b8e149 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e422 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X1 (M.op X2 X3)) X2)) = (M.op (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X2)) X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e387 X0 X1 X2 X3 x
               have i₂ := b8e394 (M.op X0 (M.op (M.op X1 (M.op X2 X3)) X2)) X1 X2 X3 x
               grind)
            | exact superpose b8e394 b8e387
            | exact resolve b8e387 b8e394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e387 b8e394
          have b8e463 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op (M.op X0 X2) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e392 X1 (M.op (M.op X0 X2) X2) X3 (M.op X2 x)
               have i₂ := b8e149 X0 X2 x
               grind)
            | exact superpose b8e149 b8e392
            | exact resolve b8e392 b8e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e468 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X1 (M.op (σ X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e392 X1 (σ X0) X2 (σ X0)
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e392
            | exact resolve b8e392 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e469 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X0 X0))) = (M.op X1 (M.op (τ X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e392 X1 (τ X0) X2 (τ X0)
               have i₂ := b8e205 X0
               grind)
            | exact superpose b8e205 b8e392
            | exact resolve b8e392 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e542 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X4)) (M.op X1 X2)) = X0 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e13 X0 (M.op X1 X2) X3
               have i₂ := b8e392 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X2 X4
               grind)
            | (have i₁ := b8e13 X0 (M.op X1 X2) X3
               have i₂ := b8e392 (M.op X0 (M.op (M.op X1 X2) X3)) X1 X4 X2
               grind)
            | exact superpose b8e392 b8e13
            | exact resolve b8e13 b8e392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e667 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op (M.op X0 X2) X2)) = (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b8e463 (M.op (M.op X0 X2) X2) X1 (M.op X2 X3) X4
               have i₂ := b8e149 X0 X2 X3
               grind)
            | exact superpose b8e149 b8e463
            | exact resolve b8e463 b8e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463
          have b8e899 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ (σ X0)) X2)) = (M.op X1 (σ (σ (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e468 (σ X0) X1 X2
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e468
            | exact resolve b8e468 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1579 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e362 x X0 X1
               have i₂ := b8e392 (M.op X0 X1) X1 (σ (M.op x x)) X2
               grind)
            | (have i₁ := b8e362 x X0 X1
               have i₂ := b8e392 (M.op X0 X1) X1 X2 (σ (M.op x x))
               grind)
            | exact superpose b8e392 b8e362
            | exact resolve b8e362 b8e392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e362
          have b8e1724 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1)) = (M.op (M.op X0 (M.op (σ X1) X2)) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1579 (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1)) (σ X1) X2
               have i₂ := b8e168 X1 X0
               grind)
            | exact superpose b8e168 b8e1579
            | exact resolve b8e1579 b8e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2134 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ X1) X2)) (σ X1)) = (M.op (M.op X0 (σ X1)) (σ (M.op X1 X1))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e403 X1 (M.op (M.op X0 (M.op (σ X1) X2)) (σ X1))
               have i₂ := b8e13 X0 (σ X1) X2
               grind)
            | exact superpose b8e13 b8e403
            | exact resolve b8e403 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2139 : ∀ X0 X1 : G, (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1)) = (M.op (M.op X0 (σ X1)) (σ (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e403 X1 (M.op (M.op X0 (σ (M.op X1 X1))) (σ X1))
               have i₂ := b8e168 X1 X0
               grind)
            | exact superpose b8e168 b8e403
            | exact resolve b8e403 b8e168
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e2782 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e113 x y
               grind)
            | exact superpose b8e113 b8e20
            | (have j1 := b8e113 x y
               grind)
            | exact resolve b8e20 b8e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e2861 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e2782
               have r₂ := b8e175
               grind)
            | exact resolve b8e2782 b8e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e175 b8e2782
          have b8e10183 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e2861
               have i₂ := b8e261
               grind)
            | exact superpose b8e261 b8e2861
            | exact resolve b8e2861 b8e261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e261 b8e2861
          have b8e10202 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
          clear b8e10183
          have b8e10231 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e10202
               grind)
            | exact superpose b8e10202 b8e14
            | exact resolve b8e14 b8e10202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10202
          have b8e10273 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e10231
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e10231
            | exact resolve b8e10231 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10231
          have b8e10274 : x = (M.op y y) := by grind
          clear b8e10273
          have b8e10525 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X4) X5)) = (M.op (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) (M.op X1 X3)) (M.op X1 X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e150 X0 (M.op X1 X2) X4 X5
               have i₂ := b8e392 (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) X1 X2 X3
               grind)
            | (have i₁ := b8e150 X0 (M.op X1 X2) X4 X5
               have i₂ := b8e392 (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X2)) X1 X3 X2
               grind)
            | exact superpose b8e392 b8e150
            | exact resolve b8e150 b8e392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10532 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (M.op X0 (M.op (M.op X1 X4) X5)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e150 X0 X1 X2 X3
               have i₂ := b8e150 X0 X1 X4 X5
               grind)
            | exact superpose b8e150 b8e150
            | exact resolve b8e150 b8e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e10842 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op (M.op (M.op X1 X2) X4) X5)) = (M.op (M.op (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) (M.op X1 X3)) (M.op X1 X2)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b8e10525 X0 X1 X2 X3 X4 X5
               have i₂ := b8e159 X1 X2 X0
               grind)
            | exact superpose b8e159 b8e10525
            | exact resolve b8e10525 b8e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10525
          have b8e10985 : ∀ X0 X1 X2 X4 X5 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op X1 X2) X4) X5)) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b8e10842 X0 X1 X2 x X4 X5
               have i₂ := b8e542 (M.op X0 X1) X1 X2 X2 x
               grind)
            | exact superpose b8e542 b8e10842
            | exact resolve b8e10842 b8e542
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e542 b8e10842
          have b8e11284 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ y)) (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e168 y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e168
            | exact resolve b8e168 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e168
          have b8e11289 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b8e390 y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e390
            | exact resolve b8e390 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e390
          have b8e11290 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ y)) (σ y)) (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e403 y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e403
            | exact resolve b8e403 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11291 : ∀ X0 : G, (M.op (M.op (M.op X0 (τ y)) (τ y)) (τ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e404 y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e404
            | exact resolve b8e404 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e404
          have b8e11292 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e468 y X0 X1
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e468
            | exact resolve b8e468 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11293 : ∀ X0 X1 : G, (M.op X0 (τ x)) = (M.op X0 (M.op (τ y) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e469 y X0 X1
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e469
            | exact resolve b8e469 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11296 : ∀ X0 : G, (M.op (M.op (M.op X0 x) y) y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e13 X0 y y
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e13
            | exact resolve b8e13 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11299 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 (M.op x X1)) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e29 X0 y y x
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e29
            | exact resolve b8e29 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11300 : ∀ X0 : G, (M.op (M.op (M.op X0 y) y) x) = X0 := by
            intro X0
            first
            | (have i₁ := b8e149 X0 y y
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e149
            | exact resolve b8e149 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11301 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b8e149 y y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e149
            | exact resolve b8e149 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149
          have b8e11306 : ∀ X0 X1 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e384 X0 y y X1
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e384
            | exact resolve b8e384 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11309 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 y X1 y
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e392
            | exact resolve b8e392 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11312 : ∀ X0 : G, y = (M.op (M.op x (M.op y X0)) y) := by
            intro X0
            first
            | (have i₁ := b8e1579 y y X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e1579
            | exact resolve b8e1579 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11314 : ∀ X0 : G, (M.op (M.op X0 x) y) = (M.op (M.op X0 y) x) := by
            intro X0
            first
            | (have i₁ := b8e11306 X0 x
               have i₂ := b8e11309 (M.op X0 y) x
               grind)
            | exact superpose b8e11309 b8e11306
            | exact resolve b8e11306 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11306
          have b8e11315 : y = (M.op (M.op x y) x) := by
            first
            | (have i₁ := b8e11301 x
               have i₂ := b8e11309 (M.op x y) x
               grind)
            | exact superpose b8e11309 b8e11301
            | exact resolve b8e11301 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11301
          have b8e11318 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
            first
            | (have i₁ := b8e11289 x
               have i₂ := b8e11292 (M.op (σ x) (σ y)) x
               grind)
            | exact superpose b8e11292 b8e11289
            | exact resolve b8e11289 b8e11292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11289
          have b8e11331 : y = (M.op (M.op x x) y) := by
            first
            | (have i₁ := b8e11315
               have i₂ := b8e11314 x
               grind)
            | exact superpose b8e11314 b8e11315
            | exact resolve b8e11315 b8e11314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11315
          have b8e12442 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) (M.op y X0)) y) = (M.op y (M.op y X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e384 (M.op x x) y X0 X1
               have i₂ := b8e11331
               grind)
            | exact superpose b8e11331 b8e384
            | exact resolve b8e384 b8e11331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11331
          have b8e12450 : ∀ X0 : G, (M.op y x) = (M.op (M.op (M.op x x) (M.op y X0)) y) := by
            intro X0
            first
            | (have i₁ := b8e12442 X0 x
               have i₂ := b8e11309 y x
               grind)
            | exact superpose b8e11309 b8e12442
            | exact resolve b8e12442 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12442
          have b8e12467 : (M.op y x) = (M.op (M.op (M.op x x) x) y) := by
            first
            | (have i₁ := b8e12450 x
               have i₂ := b8e11309 (M.op x x) x
               grind)
            | exact superpose b8e11309 b8e12450
            | exact resolve b8e12450 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12450
          have b8e12594 : ∀ X0 X1 : G, (M.op (M.op X0 y) y) = (M.op (M.op X0 x) (M.op x X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e11296 (M.op (M.op X0 x) (M.op x X1))
               have i₂ := b8e1579 X0 x X1
               grind)
            | exact superpose b8e1579 b8e11296
            | exact resolve b8e11296 b8e1579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1579 b8e11296
          have b8e12783 : ∀ X0 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 y) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b8e159 y y x
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e159
            | exact resolve b8e159 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e13069 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 x) x) x) = (M.op (M.op (M.op X0 y) y) (M.op (M.op x X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e150 (M.op (M.op X0 y) y) x X1 X2
               have i₂ := b8e11300 X0
               grind)
            | exact superpose b8e11300 b8e150
            | exact resolve b8e150 b8e11300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11300
          have b8e14075 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op (M.op y X0) x))) = (M.op X1 (M.op (σ (M.op y X0)) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e468 (M.op y X0) X1 X2
               have i₂ := b8e11309 (M.op y X0) X0
               grind)
            | exact superpose b8e11309 b8e468
            | exact resolve b8e468 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e14115 : ∀ X0 X1 : G, (M.op (M.op X0 y) (M.op (M.op y X1) X1)) = (M.op (M.op X0 (M.op y X1)) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e159 y X1 X0
               have i₂ := b8e11309 (M.op X0 (M.op y X1)) X1
               grind)
            | exact superpose b8e11309 b8e159
            | exact resolve b8e159 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e14187 : ∀ X0 X1 : G, (M.op (M.op X0 x) x) = (M.op (M.op X0 y) (M.op (M.op y X1) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14115 X0 X1
               have i₂ := b8e11309 X0 X1
               grind)
            | exact superpose b8e11309 b8e14115
            | exact resolve b8e14115 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14115
          have b8e19595 : ∀ X0 X2 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (σ y) X2)) := by
            intro X0 X2
            first
            | (have i₁ := b8e384 X0 (σ y) x X2
               have i₂ := b8e11292 X0 x
               grind)
            | exact superpose b8e11292 b8e384
            | exact resolve b8e384 b8e11292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e19889 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e19595 X0 x
               have i₂ := b8e11292 (M.op X0 (σ y)) x
               grind)
            | exact superpose b8e11292 b8e19595
            | exact resolve b8e19595 b8e11292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11292 b8e19595
          have b8e20989 : ∀ X0 X2 : G, (M.op (M.op X0 (τ x)) (τ y)) = (M.op (M.op X0 (τ y)) (M.op (τ y) X2)) := by
            intro X0 X2
            first
            | (have i₁ := b8e384 X0 (τ y) x X2
               have i₂ := b8e11293 X0 x
               grind)
            | exact superpose b8e11293 b8e384
            | exact resolve b8e384 b8e11293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21290 : ∀ X0 : G, (M.op (M.op X0 (τ x)) (τ y)) = (M.op (M.op X0 (τ y)) (τ x)) := by
            intro X0
            first
            | (have i₁ := b8e20989 X0 x
               have i₂ := b8e11293 (M.op X0 (τ y)) x
               grind)
            | exact superpose b8e11293 b8e20989
            | exact resolve b8e20989 b8e11293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11293 b8e20989
          have b8e21809 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y X1))) = (M.op (M.op (M.op (M.op X0 x) y) x) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e324 X0 x y X1
               have i₂ := b8e11312 X1
               grind)
            | exact superpose b8e11312 b8e324
            | exact resolve b8e324 b8e11312
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11312
          have b8e22122 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y X1))) = (M.op (M.op (M.op (M.op X0 x) x) y) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e21809 X0 X1
               have i₂ := b8e11314 (M.op X0 x)
               grind)
            | exact superpose b8e11314 b8e21809
            | exact resolve b8e21809 b8e11314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21809
          have b8e22426 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op y X1))) = (M.op (M.op (M.op (M.op X0 x) x) x) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e22122 X0 X1
               have i₂ := b8e11314 (M.op (M.op X0 x) x)
               grind)
            | exact superpose b8e11314 b8e22122
            | exact resolve b8e22122 b8e11314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22122
          have b8e22669 : ∀ X0 : G, (M.op X0 (M.op x x)) = (M.op (M.op (M.op (M.op X0 x) x) x) y) := by
            intro X0
            first
            | (have i₁ := b8e22426 X0 x
               have i₂ := b8e11309 x x
               grind)
            | exact superpose b8e11309 b8e22426
            | exact resolve b8e22426 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22426
          have b8e25284 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ y) (σ x))) := by
            intro X0
            first
            | (have i₁ := b8e159 (M.op (σ x) (σ y)) (σ x) x
               have i₂ := b8e11318
               grind)
            | exact superpose b8e11318 b8e159
            | exact resolve b8e159 b8e11318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e159
          have b8e25299 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) (M.op (σ x) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b8e384 X0 (M.op (σ x) (σ y)) X1 (σ x)
               have i₂ := b8e11318
               grind)
            | exact superpose b8e11318 b8e384
            | exact resolve b8e384 b8e11318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11318
          have b8e25308 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e25299 X0 x
               have i₂ := b8e29 X0 (σ x) (σ y) x
               grind)
            | exact superpose b8e29 b8e25299
            | exact resolve b8e25299 b8e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29 b8e25299
          have b8e25323 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op y y))) := by
            intro X0
            first
            | (have i₁ := b8e25284 X0
               have i₂ := b8e468 y (M.op X0 (M.op (σ x) (σ y))) (σ x)
               grind)
            | exact superpose b8e468 b8e25284
            | exact resolve b8e25284 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25284
          have b8e25337 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (M.op X0 (σ (M.op x x))) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e25308 X0
               have i₂ := b8e468 x X0 (σ y)
               grind)
            | exact superpose b8e468 b8e25308
            | exact resolve b8e25308 b8e468
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25308
          have b8e25351 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e25323 X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e25323
            | exact resolve b8e25323 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25323
          have b8e25368 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (σ (M.op x x))) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e25351 X0
               have i₂ := b8e1724 X0 x (σ y)
               grind)
            | exact superpose b8e1724 b8e25351
            | exact resolve b8e25351 b8e1724
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1724 b8e25351
          have b8e25382 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op X0 (σ x)) (σ (M.op x x))) := by
            intro X0
            first
            | (have i₁ := b8e25368 X0
               have i₂ := b8e2139 X0 x
               grind)
            | exact superpose b8e2139 b8e25368
            | exact resolve b8e25368 b8e2139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2139 b8e25368
          have b8e27372 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) x) (M.op y (M.op X0 X1))) = (M.op (M.op (M.op (M.op y x) (M.op (M.op y (M.op X0 X1)) X0)) y) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e324 (M.op (M.op x x) x) y X0 X1
               have i₂ := b8e12467
               grind)
            | exact superpose b8e12467 b8e324
            | exact resolve b8e324 b8e12467
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e324 b8e12467
          have b8e27408 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op y x) y) (M.op (M.op y (M.op X0 X1)) X0)) y) = (M.op (M.op (M.op x x) x) (M.op y (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e27372 X0 X1
               have i₂ := b8e422 (M.op y x) y X0 X1
               grind)
            | exact superpose b8e422 b8e27372
            | exact resolve b8e27372 b8e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27372
          have b8e27435 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) y) (M.op (M.op y (M.op X0 X1)) X0)) y) := by
            intro X0 X1
            first
            | (have i₁ := b8e27408 X0 X1
               have i₂ := b8e11309 (M.op (M.op x x) x) (M.op X0 X1)
               grind)
            | exact superpose b8e11309 b8e27408
            | exact resolve b8e27408 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27408
          have b8e27454 : ∀ X0 X1 : G, (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) y) y) (M.op (M.op y (M.op X0 X1)) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e27435 X0 X1
               have i₂ := b8e422 (M.op (M.op y x) y) y X0 X1
               grind)
            | exact superpose b8e422 b8e27435
            | exact resolve b8e27435 b8e422
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e422 b8e27435
          have b8e27467 : ∀ X0 : G, (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) y) y) (M.op (M.op y X0) X0)) := by
            intro X0
            first
            | (have i₁ := b8e27454 X0 x
               have i₂ := b8e667 y (M.op (M.op (M.op y x) y) y) X0 x X0
               grind)
            | exact superpose b8e667 b8e27454
            | exact resolve b8e27454 b8e667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e667 b8e27454
          have b8e27470 : (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) y) x) x) := by
            first
            | (have i₁ := b8e27467 x
               have i₂ := b8e14187 (M.op (M.op y x) y) x
               grind)
            | exact superpose b8e14187 b8e27467
            | exact resolve b8e27467 b8e14187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14187 b8e27467
          have b8e27472 : (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) x) y) x) := by
            first
            | (have i₁ := b8e27470
               have i₂ := b8e11314 (M.op y x)
               grind)
            | exact superpose b8e11314 b8e27470
            | exact resolve b8e27470 b8e11314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27470
          have b8e27473 : (M.op (M.op (M.op x x) x) x) = (M.op (M.op (M.op (M.op y x) x) x) y) := by
            first
            | (have i₁ := b8e27472
               have i₂ := b8e11314 (M.op (M.op y x) x)
               grind)
            | exact superpose b8e11314 b8e27472
            | exact resolve b8e27472 b8e11314
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11314 b8e27472
          have b8e27474 : (M.op (M.op (M.op x x) x) x) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b8e27473
               have i₂ := b8e22669 y
               grind)
            | exact superpose b8e22669 b8e27473
            | exact resolve b8e27473 b8e22669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22669 b8e27473
          have b8e45950 : (σ x) = (M.op (M.op (σ (M.op x x)) (σ y)) (σ y)) := by
            first
            | (have i₁ := b8e11284 (σ x)
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e11284
            | exact resolve b8e11284 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e51473 : (σ y) = (M.op (M.op (σ (M.op y y)) (σ y)) (σ x)) := by
            first
            | (have i₁ := b8e11290 (σ y)
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e11290
            | exact resolve b8e11290 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11290
          have b8e51590 : (σ y) = (M.op (M.op (σ (M.op y y)) (σ x)) (σ y)) := by
            first
            | (have i₁ := b8e51473
               have i₂ := b8e19889 (σ (M.op y y))
               grind)
            | exact superpose b8e19889 b8e51473
            | exact resolve b8e51473 b8e19889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19889 b8e51473
          have b8e51667 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) := by
            first
            | (have i₁ := b8e51590
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e51590
            | exact resolve b8e51590 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51590
          have b8e51712 : (σ y) = (M.op (σ (M.op x x)) (σ y)) := by
            first
            | (have i₁ := b8e51667
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e51667
            | exact resolve b8e51667 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51667
          have b8e51935 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ (M.op x x)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 (σ (M.op x x)) X1 (σ y)
               have i₂ := b8e51712
               grind)
            | exact superpose b8e51712 b8e392
            | exact resolve b8e392 b8e51712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e52907 : (τ y) = (M.op (M.op (τ (M.op y y)) (τ y)) (τ x)) := by
            first
            | (have i₁ := b8e11291 (τ y)
               have i₂ := b8e205 y
               grind)
            | exact superpose b8e205 b8e11291
            | exact resolve b8e11291 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11291
          have b8e53020 : (τ y) = (M.op (M.op (τ (M.op y y)) (τ x)) (τ y)) := by
            first
            | (have i₁ := b8e52907
               have i₂ := b8e21290 (τ (M.op y y))
               grind)
            | exact superpose b8e21290 b8e52907
            | exact resolve b8e52907 b8e21290
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21290 b8e52907
          have b8e53099 : (τ y) = (M.op (M.op (τ x) (τ x)) (τ y)) := by
            first
            | (have i₁ := b8e53020
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e53020
            | exact resolve b8e53020 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e53020
          have b8e53146 : (τ y) = (M.op (τ (M.op x x)) (τ y)) := by
            first
            | (have i₁ := b8e53099
               have i₂ := b8e205 x
               grind)
            | exact superpose b8e205 b8e53099
            | exact resolve b8e53099 b8e205
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e205 b8e53099
          have b8e56109 : ∀ X0 X1 : G, (M.op X0 (τ y)) = (M.op X0 (M.op (τ (M.op x x)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 (τ (M.op x x)) X1 (τ y)
               have i₂ := b8e53146
               grind)
            | exact superpose b8e53146 b8e392
            | exact resolve b8e392 b8e53146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e392 b8e53146
          have b8e59418 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op x x))) = (M.op X0 (M.op (M.op (σ y) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e10985 X0 (σ (M.op x x)) (σ y) X1 X2
               have i₂ := b8e51712
               grind)
            | exact superpose b8e51712 b8e10985
            | exact resolve b8e10985 b8e51712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74173 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x x)) X1)) = (M.op X0 (σ (M.op (M.op x y) y))) := by
            intro X0 X1
            first
            | (have i₁ := b8e468 (M.op x x) X0 X1
               have i₂ := b8e12594 x x
               grind)
            | exact superpose b8e12594 b8e468
            | exact resolve b8e468 b8e12594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e468
          have b8e74174 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (M.op x x)) X1)) = (M.op X0 (τ (M.op (M.op x y) y))) := by
            intro X0 X1
            first
            | (have i₁ := b8e469 (M.op x x) X0 X1
               have i₂ := b8e12594 x x
               grind)
            | exact superpose b8e12594 b8e469
            | exact resolve b8e469 b8e12594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e469
          have b8e74330 : ∀ X0 : G, (M.op X0 (τ y)) = (M.op X0 (τ (M.op (M.op x y) y))) := by
            intro X0
            first
            | (have i₁ := b8e74174 X0 x
               have i₂ := b8e56109 X0 x
               grind)
            | exact superpose b8e56109 b8e74174
            | exact resolve b8e74174 b8e56109
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56109 b8e74174
          have b8e74331 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op (M.op x y) y))) := by
            intro X0
            first
            | (have i₁ := b8e74173 X0 x
               have i₂ := b8e51935 X0 x
               grind)
            | exact superpose b8e51935 b8e74173
            | exact resolve b8e74173 b8e51935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74173
          have b8e83665 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ (M.op x x)) (M.op (M.op (σ y) X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e150 (σ (M.op x x)) (σ y) X0 X1
               have i₂ := b8e45950
               grind)
            | exact superpose b8e45950 b8e150
            | exact resolve b8e150 b8e45950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83749 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (σ x) X1) X2)) = (M.op X0 (M.op (σ (M.op x x)) (σ y))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e10985 X0 (M.op (σ (M.op x x)) (σ y)) (σ y) X1 X2
               have i₂ := b8e45950
               grind)
            | exact superpose b8e45950 b8e10985
            | exact resolve b8e10985 b8e45950
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e45950
          have b8e83750 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (M.op (σ x) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e83749 X0 X1 X2
               have i₂ := b8e51935 X0 (σ y)
               grind)
            | exact superpose b8e51935 b8e83749
            | exact resolve b8e83749 b8e51935
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51935 b8e83749
          have b8e83813 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
            first
            | (have i₁ := b8e83665 x x
               have i₂ := b8e59418 (σ (M.op x x)) x x
               grind)
            | exact superpose b8e59418 b8e83665
            | exact resolve b8e83665 b8e59418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83665
          have b8e83870 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
            first
            | (have i₁ := b8e83813
               have i₂ := b8e49 (M.op x x)
               grind)
            | exact superpose b8e49 b8e83813
            | exact resolve b8e83813 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83813
          have b8e83908 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b8e83870
               have i₂ := b8e12594 x x
               grind)
            | exact superpose b8e12594 b8e83870
            | exact resolve b8e83870 b8e12594
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12594 b8e83870
          have b8e87942 : (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (σ (M.op (τ (M.op (M.op x y) y)) (τ y))) := by
            first
            | (have i₁ := b8e51 (M.op (M.op x y) y)
               have i₂ := b8e74330 (τ (M.op (M.op x y) y))
               grind)
            | exact superpose b8e74330 b8e51
            | exact resolve b8e51 b8e74330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51
          have b8e87961 : (M.op (M.op (M.op x x) x) x) = (σ (M.op (τ (M.op (M.op x y) y)) (τ y))) := by
            first
            | (have i₁ := b8e87942
               have i₂ := b8e13069 x y y
               grind)
            | exact superpose b8e13069 b8e87942
            | exact resolve b8e87942 b8e13069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87942
          have b8e87998 : (M.op y (M.op x x)) = (σ (M.op (τ (M.op (M.op x y) y)) (τ y))) := by
            first
            | (have i₁ := b8e87961
               have i₂ := b8e27474
               grind)
            | exact superpose b8e27474 b8e87961
            | exact resolve b8e87961 b8e27474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87961
          have b8e88808 : (M.op (σ (M.op (M.op x y) y)) (σ y)) = (σ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))) := by
            first
            | (have i₁ := b8e49 (M.op (M.op x y) y)
               have i₂ := b8e74331 (σ (M.op (M.op x y) y))
               grind)
            | exact superpose b8e74331 b8e49
            | exact resolve b8e49 b8e74331
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74331
          have b8e88831 : (M.op (σ (M.op (M.op x y) y)) (σ y)) = (σ (M.op (M.op (M.op x x) x) x)) := by
            first
            | (have i₁ := b8e88808
               have i₂ := b8e13069 x y y
               grind)
            | exact superpose b8e13069 b8e88808
            | exact resolve b8e88808 b8e13069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e13069 b8e88808
          have b8e88867 : (M.op (σ (M.op (M.op x y) y)) (σ y)) = (σ (M.op y (M.op x x))) := by
            first
            | (have i₁ := b8e88831
               have i₂ := b8e27474
               grind)
            | exact superpose b8e27474 b8e88831
            | exact resolve b8e88831 b8e27474
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27474 b8e88831
          have b8e111136 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (σ (τ (M.op (M.op x y) y)))) X1)) = (M.op X0 (σ (σ (M.op (τ (M.op (M.op x y) y)) (τ y))))) := by
            intro X0 X1
            first
            | (have i₁ := b8e899 (τ (M.op (M.op x y) y)) X0 X1
               have i₂ := b8e74330 (τ (M.op (M.op x y) y))
               grind)
            | exact superpose b8e74330 b8e899
            | exact resolve b8e899 b8e74330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e899 b8e74330
          have b8e111519 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y (M.op x x)))) = (M.op X0 (M.op (σ (σ (τ (M.op (M.op x y) y)))) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e111136 X0 X1
               have i₂ := b8e87998
               grind)
            | exact superpose b8e87998 b8e111136
            | exact resolve b8e111136 b8e87998
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e87998 b8e111136
          have b8e111552 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op (M.op x y) y)) X1)) = (M.op X0 (σ (M.op y (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e111519 X0 X1
               have i₂ := b8e15 (M.op (M.op x y) y)
               grind)
            | exact superpose b8e15 b8e111519
            | exact resolve b8e111519 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111519
          have b8e156108 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ y) X0) X1)) = (M.op (M.op (σ (M.op (M.op x y) y)) (σ y)) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e150 (σ x) (σ y) X0 X1
               have i₂ := b8e83908
               grind)
            | exact superpose b8e83908 b8e150
            | exact resolve b8e150 b8e83908
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e156154 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) = (M.op X0 (M.op (σ (M.op (M.op x y) y)) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e10532 X0 (M.op (σ x) (σ y)) X1 X2 (σ y) X3
               have i₂ := b8e83908
               grind)
            | exact superpose b8e83908 b8e10532
            | exact resolve b8e10532 b8e83908
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10532 b8e83908
          have b8e156159 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op y (M.op x x)))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e156154 X0 X1 X2 x
               have i₂ := b8e111552 X0 x
               grind)
            | exact superpose b8e111552 b8e156154
            | exact resolve b8e156154 b8e111552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e111552 b8e156154
          have b8e156193 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ y) X0) X1)) = (M.op (σ (M.op y (M.op x x))) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e156108 X0 X1
               have i₂ := b8e88867
               grind)
            | exact superpose b8e88867 b8e156108
            | exact resolve b8e156108 b8e88867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88867 b8e156108
          have b8e156199 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ (M.op y (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b8e156159 X0 x x
               have i₂ := b8e10985 X0 (σ x) (σ y) x x
               grind)
            | exact superpose b8e10985 b8e156159
            | exact resolve b8e156159 b8e10985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10985 b8e156159
          have b8e156222 : (M.op (σ x) (σ (M.op x x))) = (M.op (σ (M.op y (M.op x x))) (σ y)) := by
            first
            | (have i₁ := b8e156193 x x
               have i₂ := b8e59418 (σ x) x x
               grind)
            | exact superpose b8e59418 b8e156193
            | exact resolve b8e156193 b8e59418
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59418 b8e156193
          have b8e156795 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ x)) (σ (M.op (M.op y (M.op x x)) (M.op y (M.op x x))))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e403 (M.op y (M.op x x)) X0
               have i₂ := b8e156199 (M.op X0 (σ (M.op y (M.op x x))))
               grind)
            | exact superpose b8e156199 b8e403
            | exact resolve b8e403 b8e156199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e403
          have b8e156816 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (M.op (σ (M.op y (M.op x x))) (τ (M.op X1 X1)))) (σ x)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e361 X1 X0 (σ (M.op y (M.op x x)))
               have i₂ := b8e156199 (M.op (M.op X0 (σ (M.op y (M.op x x)))) (M.op (σ (M.op y (M.op x x))) (τ (M.op X1 X1))))
               grind)
            | exact superpose b8e156199 b8e361
            | exact resolve b8e361 b8e156199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e361
          have b8e156854 : (M.op (σ (M.op y (M.op x x))) (σ x)) = (σ (M.op (M.op y (M.op x x)) (M.op y (M.op x x)))) := by
            first
            | (have i₁ := b8e49 (M.op y (M.op x x))
               have i₂ := b8e156199 (σ (M.op y (M.op x x)))
               grind)
            | exact superpose b8e156199 b8e49
            | exact resolve b8e49 b8e156199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e156919 : (M.op (σ (M.op y (M.op x x))) (σ x)) = (σ (M.op (M.op y (M.op x x)) x)) := by
            first
            | (have i₁ := b8e156854
               have i₂ := b8e11309 (M.op y (M.op x x)) (M.op x x)
               grind)
            | exact superpose b8e11309 b8e156854
            | exact resolve b8e156854 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156854
          have b8e156920 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ (M.op (M.op y (M.op x x)) x))) (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156816 X0 x
               have i₂ := b8e14075 (M.op x x) (M.op X0 (σ (M.op y (M.op x x)))) (τ (M.op x x))
               grind)
            | exact superpose b8e14075 b8e156816
            | exact resolve b8e156816 b8e14075
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e14075 b8e156816
          have b8e156931 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ x)) (σ (M.op (M.op y (M.op x x)) x))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156795 X0
               have i₂ := b8e11309 (M.op y (M.op x x)) (M.op x x)
               grind)
            | exact superpose b8e11309 b8e156795
            | exact resolve b8e156795 b8e11309
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11309 b8e156795
          have b8e156957 : (σ (M.op (M.op y y) y)) = (M.op (σ (M.op y (M.op x x))) (σ x)) := by
            first
            | (have i₁ := b8e156919
               have i₂ := b8e11299 y x
               grind)
            | exact superpose b8e11299 b8e156919
            | exact resolve b8e156919 b8e11299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156919
          have b8e156958 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ (M.op (M.op y y) y))) (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156920 X0
               have i₂ := b8e11299 y x
               grind)
            | exact superpose b8e11299 b8e156920
            | exact resolve b8e156920 b8e11299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156920
          have b8e156964 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ x)) (σ (M.op (M.op y y) y))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156931 X0
               have i₂ := b8e11299 y x
               grind)
            | exact superpose b8e11299 b8e156931
            | exact resolve b8e156931 b8e11299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11299 b8e156931
          have b8e156979 : (σ (M.op x y)) = (M.op (σ (M.op y (M.op x x))) (σ x)) := by
            first
            | (have i₁ := b8e156957
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e156957
            | exact resolve b8e156957 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156957
          have b8e156980 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ (M.op x y))) (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156958 X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e156958
            | exact resolve b8e156958 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156958
          have b8e156985 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ (M.op y (M.op x x)))) (σ x)) (σ (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156964 X0
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e156964
            | exact resolve b8e156964 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156964
          have b8e156997 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ (M.op x y))) (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156980 X0
               have i₂ := b8e156199 X0
               grind)
            | exact superpose b8e156199 b8e156980
            | exact resolve b8e156980 b8e156199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156980
          have b8e157002 : ∀ X0 : G, (M.op (M.op (M.op X0 (σ x)) (σ x)) (σ (M.op x y))) = X0 := by
            intro X0
            first
            | (have i₁ := b8e156985 X0
               have i₂ := b8e156199 X0
               grind)
            | exact superpose b8e156199 b8e156985
            | exact resolve b8e156985 b8e156199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156199 b8e156985
          have b8e157556 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op y (M.op x x))) (M.op (σ x) X0)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e384 (σ (M.op y (M.op x x))) (σ x) X0 X1
               have i₂ := b8e156979
               grind)
            | exact superpose b8e156979 b8e384
            | exact resolve b8e384 b8e156979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e384
          have b8e157578 : ∀ X1 : G, (M.op (M.op (σ (M.op y (M.op x x))) (σ x)) (σ (M.op x x))) = (M.op (σ (M.op x y)) (M.op (σ x) X1)) := by
            intro X1
            first
            | (have i₁ := b8e157556 x X1
               have i₂ := b8e2134 (σ (M.op y (M.op x x))) x x
               grind)
            | exact superpose b8e2134 b8e157556
            | exact resolve b8e157556 b8e2134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2134 b8e157556
          have b8e157600 : ∀ X1 : G, (M.op (σ (M.op x y)) (M.op (σ x) X1)) = (M.op (M.op (σ (M.op y (M.op x x))) (σ y)) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e157578 X1
               have i₂ := b8e25382 (σ (M.op y (M.op x x)))
               grind)
            | exact superpose b8e25382 b8e157578
            | exact resolve b8e157578 b8e25382
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25382 b8e157578
          have b8e157616 : ∀ X1 : G, (M.op (σ (M.op x y)) (M.op (σ x) X1)) = (M.op (M.op (σ x) (σ (M.op x x))) (σ y)) := by
            intro X1
            first
            | (have i₁ := b8e157600 X1
               have i₂ := b8e156222
               grind)
            | exact superpose b8e156222 b8e157600
            | exact resolve b8e157600 b8e156222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156222 b8e157600
          have b8e157624 : ∀ X1 : G, (M.op (M.op (σ x) (σ x)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X1)) := by
            intro X1
            first
            | (have i₁ := b8e157616 X1
               have i₂ := b8e25337 (σ x)
               grind)
            | exact superpose b8e25337 b8e157616
            | exact resolve b8e157616 b8e25337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25337 b8e157616
          have b8e157627 : ∀ X1 : G, (M.op (σ (M.op x x)) (σ x)) = (M.op (σ (M.op x y)) (M.op (σ x) X1)) := by
            intro X1
            first
            | (have i₁ := b8e157624 X1
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e157624
            | exact resolve b8e157624 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157624
          have b8e157731 : (σ (M.op y (M.op x x))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b8e156997 (σ (M.op y (M.op x x)))
               have i₂ := b8e156979
               grind)
            | exact superpose b8e156979 b8e156997
            | exact resolve b8e156997 b8e156979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156997
          have b8e157794 : (σ (M.op y (M.op x x))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
            first
            | (have i₁ := b8e157731
               have i₂ := b8e49 (M.op x y)
               grind)
            | exact superpose b8e49 b8e157731
            | exact resolve b8e157731 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157731
          have b8e157824 : (σ (M.op y (M.op x x))) = (M.op (σ (M.op (M.op x x) x)) (σ x)) := by
            first
            | (have i₁ := b8e157794
               have i₂ := b8e12783 x
               grind)
            | exact superpose b8e12783 b8e157794
            | exact resolve b8e157794 b8e12783
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157794
          have b8e157956 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X1)) = (M.op X0 (σ (M.op x y))) := by
            intro X0 X1
            first
            | (have i₁ := b8e157002 (M.op X0 (M.op (σ x) X1))
               have i₂ := b8e13 X0 (σ x) X1
               grind)
            | exact superpose b8e13 b8e157002
            | exact resolve b8e157002 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157002
          have b8e159045 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b8e49 (M.op x y)
               have i₂ := b8e157956 (σ (M.op x y)) X0
               grind)
            | exact superpose b8e157956 b8e49
            | exact resolve b8e49 b8e157956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157956
          have b8e159114 : (M.op (σ (M.op x x)) (σ x)) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b8e159045 x
               have i₂ := b8e157627 x
               grind)
            | exact superpose b8e157627 b8e159045
            | exact resolve b8e159045 b8e157627
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157627 b8e159045
          have b8e159288 : (M.op (σ (M.op x x)) (σ x)) = (σ (M.op (M.op x x) x)) := by
            first
            | (have i₁ := b8e159114
               have i₂ := b8e12783 x
               grind)
            | exact superpose b8e12783 b8e159114
            | exact resolve b8e159114 b8e12783
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12783 b8e159114
          have b8e167385 : ∀ X0 X1 : G, (M.op (σ (M.op x x)) (M.op (M.op (σ x) X0) X1)) = (M.op (M.op (M.op (σ (M.op (M.op x x) x)) (σ x)) (σ x)) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b8e150 (σ (M.op x x)) (σ x) X0 X1
               have i₂ := b8e159288
               grind)
            | exact superpose b8e159288 b8e150
            | exact resolve b8e150 b8e159288
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150 b8e159288
          have b8e167437 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op y (M.op x x))) (σ x)) (σ x)) = (M.op (σ (M.op x x)) (M.op (M.op (σ x) X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e167385 X0 X1
               have i₂ := b8e157824
               grind)
            | exact superpose b8e157824 b8e167385
            | exact resolve b8e167385 b8e157824
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157824 b8e167385
          have b8e167466 : (M.op (σ (M.op x x)) (σ y)) = (M.op (M.op (σ (M.op y (M.op x x))) (σ x)) (σ x)) := by
            first
            | (have i₁ := b8e167437 x x
               have i₂ := b8e83750 (σ (M.op x x)) x x
               grind)
            | exact superpose b8e83750 b8e167437
            | exact resolve b8e167437 b8e83750
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83750 b8e167437
          have b8e167485 : (M.op (σ (M.op x x)) (σ y)) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have i₁ := b8e167466
               have i₂ := b8e156979
               grind)
            | exact superpose b8e156979 b8e167466
            | exact resolve b8e167466 b8e156979
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e156979 b8e167466
          have b8e167495 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
            first
            | (have i₁ := b8e167485
               have i₂ := b8e51712
               grind)
            | exact superpose b8e51712 b8e167485
            | exact resolve b8e167485 b8e51712
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51712 b8e167485
          have b8e168956 : (σ (M.op x y)) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
            first
            | (have i₁ := b8e11284 (σ (M.op x y))
               have i₂ := b8e167495
               grind)
            | exact superpose b8e167495 b8e11284
            | exact resolve b8e11284 b8e167495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11284 b8e167495
          have b8e169054 : (σ (M.op x y)) = (M.op (σ (M.op y y)) (σ y)) := by
            first
            | (have i₁ := b8e168956
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e168956
            | exact resolve b8e168956 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e168956
          have b8e169093 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e169054
               have i₂ := b8e10274
               grind)
            | exact superpose b8e10274 b8e169054
            | exact resolve b8e169054 b8e10274
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10274 b8e169054
          have b8e169119 : False := by grind
          exact b8e169119
