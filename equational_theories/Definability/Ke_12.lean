import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_x_y_pyx_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
        have b0e43 : ∀ X0 : G, (M.op y y) = (M.op X0 x) := by
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
        have b0e86 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op y y) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e12 x X0 X1 x
             have i₂ := b0e43 x
             grind)
          | exact superpose b0e43 b0e12
          | exact resolve b0e12 b0e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e43
        have b0e94 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b0e86 X0 x
             have i₂ := b0e12 y X0 x y
             grind)
          | exact superpose b0e12 b0e86
          | exact resolve b0e86 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e86
        have b0e100 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
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
        have b0e123 : ∀ X0 : G, (M.op y x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e100 X0
             have i₂ := b0e94 x
             grind)
          | exact superpose b0e94 b0e100
          | exact resolve b0e100 b0e94
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e94 b0e100
        have b0e129 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b0e123 X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e123
          | exact resolve b0e123 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e123
        have b0e138 : x = y := by
          first
          | (have i₁ := b0e22
             have i₂ := b0e129 x
             grind)
          | exact superpose b0e129 b0e22
          | exact resolve b0e22 b0e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e129
        have b0e154 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
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
        have b0e179 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e23
             have i₂ := b0e138
             grind)
          | exact superpose b0e138 b0e23
          | exact resolve b0e23 b0e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e23 b0e138
        have b0e185 : False := by grind
        exact b0e185
      · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b1e24 : y = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e35 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 y X0 X1 y
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
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
          have b1e40 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b1e38 X0 X1 x x X4
               have i₂ := b1e13 X0 X1 x x
               grind)
            | exact superpose b1e13 b1e38
            | exact resolve b1e38 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38
          have b1e77 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b1e35 y x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e35
            | exact resolve b1e35 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e93 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b1e40 (σ y) (σ x) x
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e40
            | exact resolve b1e40 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40
          have b1e131 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e93 (σ x)
               grind)
            | exact superpose b1e93 b1e20
            | exact resolve b1e20 b1e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e93
          have b1e135 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e131
               have i₂ := b1e77 x
               grind)
            | exact superpose b1e77 b1e131
            | exact resolve b1e131 b1e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e77 b1e131
          have b1e136 : False := by grind
          exact b1e136
        · have b2e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b2e21 : y = (M.op y x) := by grind
          have b2e24 : y ≠ (M.op y y) := by grind
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
          have b2e57 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
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
          have b2e107 : ∀ X0 : G, y ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e57 y X0
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e57 X0 y
               grind)
            | exact superpose b2e57 b2e24
            | exact resolve b2e24 b2e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e57
          have b2e122 : ∀ X0 : G, y = (M.op X0 y) := by
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
          have b2e136 : False := by grind
          exact b2e136
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op y x) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ x)) := by grind
          have b3e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e20
            | exact resolve b3e20 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b3e16 (σ x) (σ x)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e16
            | (have j0 := b3e16 (σ x) (σ x)
               grind)
            | (have r₁ := b3e16 (σ x) (σ x)
               have r₂ := b3e23
               grind)
            | exact resolve b3e16 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e29 : (σ x) = (k (σ x) (σ x)) := by grind
          clear b3e28
          have b3e32 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b3e29
               have i₂ := b3e19 x x
               grind)
            | exact superpose b3e19 b3e29
            | exact resolve b3e29 b3e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e29
          have b3e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b3e13 y X0 X1 x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e45 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 (k x x)
               have i₂ := b3e32
               grind)
            | exact superpose b3e32 b3e14
            | exact resolve b3e14 b3e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e32
          have b3e46 : x = (k x x) := by
            first
            | (have i₁ := b3e45
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e45
            | exact resolve b3e45 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e45
          have b3e60 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b3e46
               have i₂ := b3e18 x x
               grind)
            | exact superpose b3e18 b3e46
            | (have j1 := b3e18 x x
               grind)
            | exact resolve b3e46 b3e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e46
          have b3e71 : x = (M.op x x) := by grind
          clear b3e60
          have b3e84 : ∀ X0 : G, (M.op y x) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b3e37 x X0
               have i₂ := b3e71
               grind)
            | exact superpose b3e71 b3e37
            | exact resolve b3e37 b3e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e37
          have b3e100 : ∀ X0 : G, y = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b3e84 X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e84
            | exact resolve b3e84 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e84
          have b3e108 : x = y := by
            first
            | (have i₁ := b3e71
               have i₂ := b3e100 x
               grind)
            | exact superpose b3e100 b3e71
            | exact resolve b3e71 b3e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e71 b3e100
          have b3e146 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e25
               have i₂ := b3e108
               grind)
            | exact superpose b3e108 b3e25
            | exact resolve b3e25 b3e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e25 b3e108
          have b3e150 : False := by grind
          exact b3e150
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b4e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b4e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
            have b4e25 : x ≠ (M.op x y) := by grind
            have b4e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e29 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b4e17 (σ x) (σ x)
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e17
              | (have j0 := b4e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b4e17 (σ x) (σ x)
                 have r₂ := b4e24
                 grind)
              | exact resolve b4e17 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e30 : (σ x) = (k (σ x) (σ x)) := by grind
            clear b4e29
            have b4e33 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b4e30
                 have i₂ := b4e20 x x
                 grind)
              | exact superpose b4e20 b4e30
              | exact resolve b4e30 b4e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30
            have b4e38 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 (k x x)
                 have i₂ := b4e33
                 grind)
              | exact superpose b4e33 b4e15
              | exact resolve b4e15 b4e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33
            have b4e39 : x = (k x x) := by
              first
              | (have i₁ := b4e38
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e38
              | exact resolve b4e38 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e38
            have b4e42 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b4e14 x X0 X1 y
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e43 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b4e14 y X0 X1 y
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e50 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b4e42 X0 x
                 have i₂ := b4e43 X0 x
                 grind)
              | exact superpose b4e43 b4e42
              | exact resolve b4e42 b4e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e42 b4e43
            have b4e58 : x ≠ (M.op y y) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e50 y
                 grind)
              | exact superpose b4e50 b4e25
              | exact resolve b4e25 b4e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e64 : x ≠ y := by
              first
              | (have i₁ := b4e58
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e58
              | exact resolve b4e58 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e58
            have b4e72 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b4e39
                 have i₂ := b4e19 x x
                 grind)
              | exact superpose b4e19 b4e39
              | (have j1 := b4e19 x x
                 grind)
              | exact resolve b4e39 b4e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e39
            have b4e84 : x = (M.op x x) := by grind
            clear b4e72
            have b4e90 : x = (M.op y x) := by
              first
              | (have i₁ := b4e84
                 have i₂ := b4e50 x
                 grind)
              | exact superpose b4e50 b4e84
              | exact resolve b4e84 b4e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e50 b4e84
            have b4e95 : x = y := by
              first
              | (have i₁ := b4e90
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e90
              | exact resolve b4e90 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e90
            have b4e99 : False := by grind
            exact b4e99
          · have b5e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op y x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b5e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b5e17 (σ x) (σ x)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e17
              | (have j0 := b5e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b5e17 (σ x) (σ x)
                 have r₂ := b5e24
                 grind)
              | exact resolve b5e17 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e29 : (σ x) = (k (σ x) (σ x)) := by grind
            clear b5e28
            have b5e31 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b5e29
                 have i₂ := b5e20 x x
                 grind)
              | exact superpose b5e20 b5e29
              | exact resolve b5e29 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e29
            have b5e36 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b5e15 (k x x)
                 have i₂ := b5e31
                 grind)
              | exact superpose b5e31 b5e15
              | exact resolve b5e15 b5e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e31
            have b5e37 : x = (k x x) := by
              first
              | (have i₁ := b5e36
                 have i₂ := b5e15 x
                 grind)
              | exact superpose b5e15 b5e36
              | exact resolve b5e36 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e36
            have b5e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 x X0 X1 y
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e47 : ∀ X0 : G, (M.op x x) = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b5e40 x X0
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e40
              | exact resolve b5e40 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e40
            have b5e67 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op (M.op x x) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 y X0 X1 x
                 have i₂ := b5e47 x
                 grind)
              | exact superpose b5e47 b5e14
              | exact resolve b5e14 b5e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e47
            have b5e71 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b5e67 X0 x
                 have i₂ := b5e14 x X0 x x
                 grind)
              | exact superpose b5e14 b5e67
              | exact resolve b5e67 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e67
            have b5e79 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b5e37
                 have i₂ := b5e19 x x
                 grind)
              | exact superpose b5e19 b5e37
              | (have j1 := b5e19 x x
                 grind)
              | exact resolve b5e37 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37
            have b5e91 : x = (M.op x x) := by grind
            clear b5e79
            have b5e96 : x = (M.op y x) := by
              first
              | (have i₁ := b5e91
                 have i₂ := b5e71 x
                 grind)
              | exact superpose b5e71 b5e91
              | exact resolve b5e91 b5e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e71 b5e91
            have b5e101 : x = y := by
              first
              | (have i₁ := b5e96
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e96
              | exact resolve b5e96 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e96
            have b5e108 : (σ y) ≠ (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e101
                 grind)
              | exact superpose b5e101 b5e23
              | exact resolve b5e23 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e109 : (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b5e24
                 have i₂ := b5e101
                 grind)
              | exact superpose b5e101 b5e24
              | exact resolve b5e24 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e101
            have b5e115 : False := by grind
            exact b5e115
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          have b6e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b6e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b6e13 (M.op (M.op X2 X0) X1) X3 X4 x
               have i₂ := b6e13 X0 X1 x X2
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e35 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b6e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b6e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b6e13 b6e13
            | exact resolve b6e13 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e37 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b6e35 X0 X1 x x X4
               have i₂ := b6e13 X0 X1 x x
               grind)
            | exact superpose b6e13 b6e35
            | exact resolve b6e35 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35
          have b6e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e34 X0 X1 X2 X3 x
               have i₂ := b6e13 X1 X3 x X0
               grind)
            | exact superpose b6e13 b6e34
            | exact resolve b6e34 b6e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e34
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
          have b6e62 : x = (M.op x x) := by
            first
            | (have i₁ := b6e24
               have i₂ := b6e39 x
               grind)
            | exact superpose b6e39 b6e24
            | exact resolve b6e24 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e63 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x x)) := by
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
          clear b6e32
          have b6e64 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b6e63 x
               have i₂ := b6e33 x x
               grind)
            | exact superpose b6e33 b6e63
            | exact resolve b6e63 b6e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e33 b6e63
          have b6e70 : y = (M.op x y) := by
            first
            | (have i₁ := b6e64
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e64
            | exact resolve b6e64 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e64
          have b6e72 : x = y := by
            first
            | (have i₁ := b6e70
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e70
            | exact resolve b6e70 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e70
          have b6e103 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e39 X0
               have i₂ := b6e72
               grind)
            | exact superpose b6e72 b6e39
            | exact resolve b6e39 b6e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39 b6e72
          have b6e104 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b6e103 X0
               have i₂ := b6e62
               grind)
            | exact superpose b6e62 b6e103
            | exact resolve b6e103 b6e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e103
          have b6e140 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b6e17 x X0
               have i₂ := b6e62
               grind)
            | exact superpose b6e62 b6e17
            | (have j0 := b6e17 x X0
               grind)
            | (have r₁ := b6e17 x x
               have r₂ := b6e62
               grind)
            | exact resolve b6e17 b6e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e62
          have b6e144 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have j0 := b6e140 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e140
          have b6e145 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b6e144 X0
               have i₂ := b6e104 X0
               grind)
            | exact superpose b6e104 b6e144
            | (have j0 := b6e144 X0
               grind)
            | exact resolve b6e144 b6e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e104 b6e144
          have b6e162 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b6e13 X1 X2 x X0
               have i₂ := b6e37 (M.op X0 X1) X2 x
               grind)
            | exact superpose b6e37 b6e13
            | exact resolve b6e13 b6e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e37
          have b6e263 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e16 X1 (M.op (M.op X2 X3) X0)
               have i₂ := b6e38 X3 X0 X2 X1
               grind)
            | exact superpose b6e38 b6e16
            | (have j0 := b6e16 X1 (M.op (M.op X2 X3) X0)
               grind)
            | (have r₁ := b6e16 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
               have r₂ := b6e38 X0 (M.op X2 X0) X2 (M.op X2 X0)
               grind)
            | exact resolve b6e16 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e271 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b6e263 X0 X1 X2 X3
               have i₂ := b6e162 X2 X3 X0
               grind)
            | exact superpose b6e162 b6e263
            | (have j0 := b6e263 X0 X1 X2 X3
               grind)
            | (have r₁ := b6e263 X2 X2 X0 X2
               have r₂ := b6e162 X0 X2 X2
               grind)
            | (have r₁ := b6e263 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
               have r₂ := b6e162 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
               grind)
            | exact resolve b6e263 b6e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e263
          have b6e277 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
            intro X0 X1 X3
            first
            | (have i₁ := b6e271 X0 X1 x X3
               have i₂ := b6e162 x X3 X0
               grind)
            | exact superpose b6e162 b6e271
            | (have j0 := b6e271 X0 X1 x X3
               grind)
            | (have r₁ := b6e271 x x x (M.op X0 x)
               have r₂ := b6e162 X0 x x
               grind)
            | (have r₁ := b6e271 (M.op X0 X1) (M.op X0 X1) x X1
               have r₂ := b6e162 X0 X1 (M.op X0 X1)
               grind)
            | exact resolve b6e271 b6e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e162 b6e271
          have b6e462 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b6e31 X0 x
               have i₂ := b6e145 (τ X0)
               grind)
            | exact superpose b6e145 b6e31
            | (have j1 := b6e145 (τ X0)
               grind)
            | exact resolve b6e31 b6e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31 b6e145
          have b6e469 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b6e462 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e462
            | (have j0 := b6e462 X0
               grind)
            | exact resolve b6e462 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e462
          have b6e1388 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have j0 := b6e277 X0 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e277
          have b6e1468 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (τ (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b6e469 (M.op (σ x) (σ x))
               have i₂ := b6e1388 (σ x)
               grind)
            | exact superpose b6e1388 b6e469
            | (have j0 := b6e469 (M.op (σ x) (σ x))
               grind)
            | exact resolve b6e469 b6e1388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e469 b6e1388
          have b6e1485 : x = (τ (M.op (σ x) (σ x))) := by
            first
            | (have r₁ := b6e1468
               have r₂ := b6e23
               grind)
            | exact resolve b6e1468 b6e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1468
          have b6e1567 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b6e15 (M.op (σ x) (σ x))
               have i₂ := b6e1485
               grind)
            | exact superpose b6e1485 b6e15
            | exact resolve b6e15 b6e1485
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e1485
          have b6e1571 : False := by grind
          exact b6e1571
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b7e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : y ≠ y ∨ y = (k y y) := by
              first
              | (have i₁ := b7e17 y y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e17
              | (have j0 := b7e17 y y
                 grind)
              | (have r₁ := b7e17 y y
                 have r₂ := b7e26
                 grind)
              | exact resolve b7e17 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : y = (k y y) := by grind
            clear b7e28
            have b7e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 y X0 X1 y
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
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
            have b7e42 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b7e40 X0 X1 x x X4
                 have i₂ := b7e14 X0 X1 x x
                 grind)
              | exact superpose b7e14 b7e40
              | exact resolve b7e40 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e61 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 X0
                 have i₂ := b7e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b7e19 b7e20
              | (have j1 := b7e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b7e20 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e82 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b7e38 y x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e38
              | exact resolve b7e38 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e533 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b7e61 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e61
            have b7e535 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b7e533 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e533
            have b7e1166 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b7e535 y
                 have i₂ := b7e29
                 grind)
              | exact superpose b7e29 b7e535
              | (have j0 := b7e535 y
                 grind)
              | exact resolve b7e535 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e535
            have b7e1173 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b7e1166
            have b7e1388 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e42 (σ y) (σ y) x
                 have i₂ := b7e1173
                 grind)
              | exact superpose b7e1173 b7e42
              | exact resolve b7e42 b7e1173
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e42 b7e1173
            have b7e1464 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b7e21
                 have i₂ := b7e1388 (σ x)
                 grind)
              | exact superpose b7e1388 b7e21
              | exact resolve b7e21 b7e1388
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1388
            have b7e1473 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b7e1464
                 have i₂ := b7e82 x
                 grind)
              | exact superpose b7e82 b7e1464
              | exact resolve b7e1464 b7e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e82 b7e1464
            have b7e1474 : False := by grind
            exact b7e1474
          · have b8e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b8e22 : y = (M.op y x) := by grind
            have b8e26 : y ≠ (M.op y y) := by grind
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
            have b8e51 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
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
            have b8e102 : ∀ X0 : G, y ≠ (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b8e26
                 have i₂ := b8e51 y X0
                 grind)
              | (have i₁ := b8e26
                 have i₂ := b8e51 X0 y
                 grind)
              | exact superpose b8e51 b8e26
              | exact resolve b8e26 b8e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e51
            have b8e108 : ∀ X0 : G, y = (M.op X0 y) := by
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
            have b8e130 : False := by grind
            exact b8e130
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b9e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b9e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b9e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = (M.op x x) := by grind
          have b9e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b9e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e25 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e20
            | exact resolve b9e20 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e28 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b9e29 : (σ x) = (k (σ x) (σ y)) := by grind
          clear b9e28
          have b9e32 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b9e29
               have i₂ := b9e19 x y
               grind)
            | exact superpose b9e19 b9e29
            | exact resolve b9e29 b9e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e29
          have b9e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b9e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b9e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b9e13 b9e13
            | exact resolve b9e13 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e41 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b9e39 X0 X1 x x X4
               have i₂ := b9e13 X0 X1 x x
               grind)
            | exact superpose b9e13 b9e39
            | exact resolve b9e39 b9e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e39
          have b9e49 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b9e17 x X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e17
            | (have j0 := b9e17 x X0
               grind)
            | (have r₁ := b9e17 x x
               have r₂ := b9e22
               grind)
            | exact resolve b9e17 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e51 : ∀ X0 : G, (k x X0) = X0 ∨ (M.op X0 x) = X0 := by
            intro X0
            first
            | (have j0 := b9e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e49
          have b9e124 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b9e41 (σ y) (σ x) x
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e41
            | exact resolve b9e41 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e41
          have b9e177 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e25
               have i₂ := b9e124 (σ x)
               grind)
            | exact superpose b9e124 b9e25
            | exact resolve b9e25 b9e124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e25 b9e124
          have b9e193 : (σ x) = (σ y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b9e32
               have i₂ := b9e51 y
               grind)
            | exact superpose b9e51 b9e32
            | (have j1 := b9e51 y
               grind)
            | exact resolve b9e32 b9e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e32 b9e51
          have b9e199 : y = (M.op y x) := by
            first
            | (have r₁ := b9e193
               have r₂ := b9e177
               grind)
            | exact resolve b9e193 b9e177
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e177 b9e193
          have b9e203 : False := by grind
          exact b9e203
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b10e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e45 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 y X0 X1 y
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e14
              | exact resolve b10e14 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e46 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b10e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b10e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e48 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b10e46 X0 X1 x x X4
                 have i₂ := b10e14 X0 X1 x x
                 grind)
              | exact superpose b10e14 b10e46
              | exact resolve b10e46 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e46
            have b10e100 : ∀ X0 : G, y = (M.op X0 y) := by
              intro X0
              first
              | (have i₁ := b10e45 y x
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e45
              | exact resolve b10e45 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e45
            have b10e119 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b10e48 (σ y) (σ x) x
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e48
              | exact resolve b10e48 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e48
            have b10e148 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b10e21
                 have i₂ := b10e119 (σ x)
                 grind)
              | exact superpose b10e119 b10e21
              | exact resolve b10e21 b10e119
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e119
            have b10e159 : (σ y) ≠ (σ y) := by
              first
              | (have i₁ := b10e148
                 have i₂ := b10e100 x
                 grind)
              | exact superpose b10e100 b10e148
              | exact resolve b10e148 b10e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e100 b10e148
            have b10e160 : False := by grind
            exact b10e160
          · have b11e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op y x) := by grind
            have b11e23 : x = (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e28 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b11e29 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b11e28
            have b11e31 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b11e29
                 have i₂ := b11e20 x y
                 grind)
              | exact superpose b11e20 b11e29
              | exact resolve b11e29 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e29
            have b11e36 : (k x y) = (τ (σ x)) := by
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
            have b11e37 : x = (k x y) := by
              first
              | (have i₁ := b11e36
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e36
              | exact resolve b11e36 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e36
            have b11e40 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b11e14 x X0 X1 x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e47 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b11e40 x x
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e40
              | exact resolve b11e40 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e40
            have b11e54 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b11e18 x X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e18
              | (have j0 := b11e18 x X0
                 grind)
              | (have r₁ := b11e18 x x
                 have r₂ := b11e23
                 grind)
              | exact resolve b11e18 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e58 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have j0 := b11e54 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e54
            have b11e61 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
              intro X0
              first
              | (have i₁ := b11e58 X0
                 have i₂ := b11e47 X0
                 grind)
              | exact superpose b11e47 b11e58
              | (have j0 := b11e58 X0
                 grind)
              | exact resolve b11e58 b11e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e58
            have b11e62 : x ≠ y := by
              first
              | (have i₁ := b11e22
                 have i₂ := b11e47 y
                 grind)
              | exact superpose b11e47 b11e22
              | exact resolve b11e22 b11e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e47
            have b11e95 : x = y ∨ x = y := by
              first
              | (have i₁ := b11e37
                 have i₂ := b11e61 y
                 grind)
              | exact superpose b11e61 b11e37
              | (have j1 := b11e61 y
                 grind)
              | exact resolve b11e37 b11e61
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e37 b11e61
            have b11e99 : x = y := by grind
            clear b11e95
            have b11e103 : False := by grind
            exact b11e103
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b12e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b12e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b12e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b12e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b12e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e22 : y ≠ (M.op y x) := by grind
            have b12e23 : x = (M.op x x) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e27 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e21
              | exact resolve b12e21 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : x ≠ x ∨ y = (k y x) := by
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
            have b12e32 : y = (k y x) := by grind
            clear b12e29
            have b12e36 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X1 (τ X0)
                 have i₂ := b12e16 X0
                 grind)
              | exact superpose b12e16 b12e20
              | exact resolve b12e20 b12e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 x X0 X1 x
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e38 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y X0) := by
              intro X0 X1
              first
              | (have i₁ := b12e14 y X0 X1 x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X4 (M.op (M.op X0 X1) X3)) := by
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
            have b12e41 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
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
            have b12e43 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b12e41 X0 X1 x x X4
                 have i₂ := b12e14 X0 X1 x x
                 grind)
              | exact superpose b12e14 b12e41
              | exact resolve b12e41 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e41
            have b12e44 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X1) X3) = (M.op X1 X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e40 X0 X1 X2 X3 x
                 have i₂ := b12e14 X1 X3 x X0
                 grind)
              | exact superpose b12e14 b12e40
              | exact resolve b12e40 b12e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40
            have b12e52 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b12e37 y x
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e37
              | exact resolve b12e37 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e66 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e20 X1 X0
                 have i₂ := b12e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b12e19 b12e20
              | (have j1 := b12e19 (σ X1) (σ X1)
                 grind)
              | exact resolve b12e20 b12e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e83 : x ≠ y := by
              first
              | (have i₁ := b12e22
                 have i₂ := b12e52 y
                 grind)
              | exact superpose b12e52 b12e22
              | exact resolve b12e22 b12e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e52
            have b12e99 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b12e37 X0 x
                 have i₂ := b12e38 X0 x
                 grind)
              | exact superpose b12e38 b12e37
              | exact resolve b12e37 b12e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e38
            have b12e128 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e14 X1 X2 x X0
                 have i₂ := b12e43 (M.op X0 X1) X2 x
                 grind)
              | exact superpose b12e43 b12e14
              | exact resolve b12e14 b12e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e181 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b12e15 (k X0 (τ X1))
                 have i₂ := b12e36 X1 X0
                 grind)
              | exact superpose b12e36 b12e15
              | exact resolve b12e15 b12e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36
            have b12e272 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op X2 X3) X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e17 X1 (M.op (M.op X2 X3) X0)
                 have i₂ := b12e44 X3 X0 X2 X1
                 grind)
              | exact superpose b12e44 b12e17
              | (have j0 := b12e17 X1 (M.op (M.op X2 X3) X0)
                 grind)
              | (have r₁ := b12e17 (M.op X2 X0) (M.op (M.op X2 X0) (M.op X2 X0))
                 have r₂ := b12e44 X0 (M.op X2 X0) X2 (M.op X2 X0)
                 grind)
              | exact resolve b12e17 b12e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e44
            have b12e281 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op (M.op X2 X3) X0)) = X1 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b12e272 X0 X1 X2 X3
                 have i₂ := b12e128 X2 X3 X0
                 grind)
              | exact superpose b12e128 b12e272
              | (have j0 := b12e272 X0 X1 X2 X3
                 grind)
              | (have r₁ := b12e272 X2 X2 X0 X2
                 have r₂ := b12e128 X0 X2 X2
                 grind)
              | (have r₁ := b12e272 (M.op X0 (M.op X2 X3)) (M.op X0 (M.op X2 X3)) X2 X3
                 have r₂ := b12e128 X0 (M.op X2 X3) (M.op X0 (M.op X2 X3))
                 grind)
              | exact resolve b12e272 b12e128
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e272
            have b12e285 : ∀ X0 X1 X3 : G, (M.op X0 X1) ≠ (M.op X3 X0) ∨ (k X1 (M.op X3 X0)) = X1 := by
              intro X0 X1 X3
              first
              | (have i₁ := b12e281 X0 X1 x X3
                 have i₂ := b12e128 x X3 X0
                 grind)
              | exact superpose b12e128 b12e281
              | (have j0 := b12e281 X0 X1 x X3
                 grind)
              | (have r₁ := b12e281 x x x (M.op X0 x)
                 have r₂ := b12e128 X0 x x
                 grind)
              | (have r₁ := b12e281 (M.op X0 X1) (M.op X0 X1) x X1
                 have r₂ := b12e128 X0 X1 (M.op X0 X1)
                 grind)
              | exact resolve b12e281 b12e128
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e128 b12e281
            have b12e688 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b12e43 (σ X0) (σ X1) x
                 have i₂ := b12e66 X0 X1
                 grind)
              | exact superpose b12e66 b12e43
              | (have j1 := b12e66 X0 X0
                 grind)
              | exact resolve b12e43 b12e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e43 b12e66
            have b12e1144 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have j0 := b12e285 X0 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e285
            have b12e1201 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
              intro X0
              first
              | (have i₁ := b12e181 X0 (M.op (σ X0) (σ X0))
                 have i₂ := b12e1144 (σ X0)
                 grind)
              | exact superpose b12e1144 b12e181
              | exact resolve b12e181 b12e1144
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e181 b12e1144
            have b12e1221 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
              intro X0
              first
              | (have i₁ := b12e1201 X0
                 have i₂ := b12e15 X0
                 grind)
              | exact superpose b12e15 b12e1201
              | exact resolve b12e1201 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1201
            have b12e4312 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              intro X0
              first
              | (have i₁ := b12e688 y x x
                 have i₂ := b12e32
                 grind)
              | exact superpose b12e32 b12e688
              | (have j0 := b12e688 y y x
                 grind)
              | exact resolve b12e688 b12e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e32 b12e688
            have b12e4424 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              intro X0
              first
              | (have j0 := b12e4312 X0
                 grind)
              | (have r₁ := b12e4312 X0
                 have r₂ := b12e27
                 grind)
              | exact resolve b12e4312 b12e27
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e27 b12e4312
            have b12e11941 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have j0 := b12e4424 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e4424
            have b12e11942 : (σ y) = (M.op (σ y) (σ y)) := by grind
            clear b12e11941
            have b12e11977 : y = (k y (τ (σ y))) := by
              first
              | (have i₁ := b12e1221 y
                 have i₂ := b12e11942
                 grind)
              | exact superpose b12e11942 b12e1221
              | exact resolve b12e1221 b12e11942
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e1221 b12e11942
            have b12e12007 : y = (k y y) := by
              first
              | (have i₁ := b12e11977
                 have i₂ := b12e15 y
                 grind)
              | exact superpose b12e15 b12e11977
              | exact resolve b12e11977 b12e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e11977
            have b12e12173 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b12e19 y y
                 have i₂ := b12e12007
                 grind)
              | exact superpose b12e12007 b12e19
              | (have j0 := b12e19 y y
                 grind)
              | exact resolve b12e19 b12e12007
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e12007
            have b12e12187 : y = (M.op y y) := by grind
            clear b12e12173
            have b12e12198 : y = (M.op x y) := by
              first
              | (have i₁ := b12e12187
                 have i₂ := b12e99 y
                 grind)
              | exact superpose b12e99 b12e12187
              | exact resolve b12e12187 b12e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e99 b12e12187
            have b12e12207 : x = y := by
              first
              | (have i₁ := b12e12198
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e12198
              | exact resolve b12e12198 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e12198
            have b12e12215 : False := by grind
            exact b12e12215
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b13e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b13e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b13e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b13e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b13e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e23 : y ≠ (M.op y x) := by grind
              have b13e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : y ≠ y ∨ y = (k y y) := by
                first
                | (have i₁ := b13e18 y y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e18
                | (have j0 := b13e18 y y
                   grind)
                | (have r₁ := b13e18 y y
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e18 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e33 : y = (k y y) := by grind
              clear b13e30
              have b13e36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 (τ X0) X1
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e21
                | exact resolve b13e21 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e37 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 (τ X0)
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e21
                | exact resolve b13e21 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 y X0 X1 y
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e42 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X2 X3 X4
                first
                | (have i₁ := b13e15 X2 (M.op (M.op X3 X0) X1) X4 x
                   have i₂ := b13e15 X0 X1 (M.op x X2) X3
                   grind)
                | exact superpose b13e15 b13e15
                | exact resolve b13e15 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e44 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b13e42 X0 X1 x x X4
                   have i₂ := b13e15 X0 X1 x x
                   grind)
                | exact superpose b13e15 b13e42
                | exact resolve b13e42 b13e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e42
              have b13e57 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = X0 ∨ (k y X0) = X0 := by
                intro X0
                first
                | (have i₁ := b13e19 y X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e19
                | (have j0 := b13e19 y X0
                   grind)
                | (have r₁ := b13e19 y x
                   have r₂ := b13e28
                   grind)
                | exact resolve b13e19 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e58 : ∀ X0 : G, (k y X0) = X0 ∨ (M.op X0 y) = X0 := by
                intro X0
                first
                | (have j0 := b13e57 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e57
              have b13e78 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b13e21 X1 X0
                   have i₂ := b13e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b13e20 b13e21
                | (have j1 := b13e20 (σ X1) (σ X1)
                   grind)
                | exact resolve b13e21 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e102 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b13e41 y x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e41
                | exact resolve b13e41 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e41
              have b13e124 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b13e44 X0 X0 x
                   have i₂ := b13e20 X0 X1
                   grind)
                | exact superpose b13e20 b13e44
                | (have j1 := b13e20 X0 X2
                   grind)
                | exact resolve b13e44 b13e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e159 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b13e16 (k (τ X0) X1)
                   have i₂ := b13e36 X0 X1
                   grind)
                | exact superpose b13e36 b13e16
                | exact resolve b13e16 b13e36
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e36
              have b13e174 : ∀ X0 : G, (σ (τ X0)) = (k (σ y) X0) ∨ (τ X0) = (M.op (τ X0) y) := by
                intro X0
                first
                | (have i₁ := b13e37 X0 y
                   have i₂ := b13e58 (τ X0)
                   grind)
                | exact superpose b13e58 b13e37
                | (have j1 := b13e58 (τ X0)
                   grind)
                | exact resolve b13e37 b13e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e37 b13e58
              have b13e177 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (τ X0) = (M.op (τ X0) y) := by
                intro X0
                first
                | (have i₁ := b13e174 X0
                   have i₂ := b13e17 X0
                   grind)
                | exact superpose b13e17 b13e174
                | (have j0 := b13e174 X0
                   grind)
                | exact resolve b13e174 b13e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e174
              have b13e178 : ∀ X0 : G, (k (σ y) X0) = X0 ∨ (τ X0) = y := by
                intro X0
                first
                | (have i₁ := b13e177 X0
                   have i₂ := b13e102 (τ X0)
                   grind)
                | exact superpose b13e102 b13e177
                | (have j0 := b13e177 X0
                   grind)
                | exact resolve b13e177 b13e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e177
              have b13e393 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ y)) X0) ∨ (τ (σ X0)) = y := by
                intro X0
                first
                | (have i₁ := b13e159 (σ y) X0
                   have i₂ := b13e178 (σ X0)
                   grind)
                | exact superpose b13e178 b13e159
                | (have j1 := b13e178 (σ X0)
                   grind)
                | exact resolve b13e159 b13e178
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e178
              have b13e400 : ∀ X0 : G, (τ (σ X0)) = (k y X0) ∨ (τ (σ X0)) = y := by
                intro X0
                first
                | (have i₁ := b13e393 X0
                   have i₂ := b13e16 y
                   grind)
                | exact superpose b13e16 b13e393
                | (have j0 := b13e393 X0
                   grind)
                | exact resolve b13e393 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e393
              have b13e405 : ∀ X0 : G, (k y X0) = X0 ∨ (τ (σ X0)) = y := by
                intro X0
                first
                | (have i₁ := b13e400 X0
                   have i₂ := b13e16 X0
                   grind)
                | exact superpose b13e16 b13e400
                | (have j0 := b13e400 X0
                   grind)
                | exact resolve b13e400 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e400
              have b13e406 : ∀ X0 : G, (k y X0) = X0 ∨ y = X0 := by
                intro X0
                first
                | (have i₁ := b13e405 X0
                   have i₂ := b13e16 X0
                   grind)
                | exact superpose b13e16 b13e405
                | (have j0 := b13e405 X0
                   grind)
                | exact resolve b13e405 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e405
              have b13e719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e78 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e78
              have b13e721 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b13e719 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e719
              have b13e1661 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b13e721 y
                   have i₂ := b13e33
                   grind)
                | exact superpose b13e33 b13e721
                | (have j0 := b13e721 y
                   grind)
                | exact resolve b13e721 b13e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e33 b13e721
              have b13e1666 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e1661
              have b13e1701 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b13e44 (σ y) (σ y) x
                   have i₂ := b13e1666
                   grind)
                | exact superpose b13e1666 b13e44
                | exact resolve b13e44 b13e1666
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e44 b13e1666
              have b13e1818 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b13e22
                   have i₂ := b13e124 (σ y) (σ x) X0
                   grind)
                | exact superpose b13e124 b13e22
                | (have j1 := b13e124 (σ y) x X0
                   grind)
                | exact resolve b13e22 b13e124
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e124
              have b13e1871 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b13e1818 X0
                   have i₂ := b13e102 x
                   grind)
                | exact superpose b13e102 b13e1818
                | (have j0 := b13e1818 X0
                   grind)
                | exact resolve b13e1818 b13e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e102 b13e1818
              have b13e1872 : ∀ X0 : G, (k (σ y) X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have j0 := b13e1871 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1871
              have b13e1875 : ∀ X0 : G, (σ y) = (k (σ y) X0) ∨ (M.op X0 (σ y)) = X0 := by
                intro X0
                first
                | (have i₁ := b13e1872 X0
                   have i₂ := b13e1701 X0
                   grind)
                | exact superpose b13e1701 b13e1872
                | (have j0 := b13e1872 X0
                   grind)
                | exact resolve b13e1872 b13e1701
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1701 b13e1872
              have b13e1876 : ∀ X0 : G, (σ y) = (k (σ y) X0) := by
                intro X0
                first
                | (have j0 := b13e1875 X0
                   have j1 := b13e18 (σ y) X0
                   grind)
                | (have r₁ := b13e1875 x
                   have r₂ := b13e18 (σ y) x
                   grind)
                | exact resolve b13e1875 b13e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1875
              have b13e1901 : ∀ X0 : G, (τ (σ y)) = (k (τ (σ y)) X0) := by
                intro X0
                first
                | (have i₁ := b13e159 (σ y) X0
                   have i₂ := b13e1876 (σ X0)
                   grind)
                | exact superpose b13e1876 b13e159
                | exact resolve b13e159 b13e1876
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e159 b13e1876
              have b13e1904 : ∀ X0 : G, y = (k y X0) := by
                intro X0
                first
                | (have i₁ := b13e1901 X0
                   have i₂ := b13e16 y
                   grind)
                | exact superpose b13e16 b13e1901
                | exact resolve b13e1901 b13e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1901
              have b13e1994 : ∀ X0 : G, y = X0 ∨ y = X0 := by
                intro X0
                first
                | (have i₁ := b13e406 X0
                   have i₂ := b13e1904 X0
                   grind)
                | exact superpose b13e1904 b13e406
                | (have j0 := b13e406 X0
                   grind)
                | exact resolve b13e406 b13e1904
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e406 b13e1904
              have b13e2011 : ∀ X0 : G, y = X0 := by
                intro X0
                first
                | (have j0 := b13e1994 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e1994
              have b13e2200 : y ≠ y := by
                first
                | (have i₁ := b13e23
                   have i₂ := b13e2011 (M.op y x)
                   grind)
                | exact superpose b13e2011 b13e23
                | (have r₁ := b13e23
                   have r₂ := b13e2011 (M.op y x)
                   grind)
                | exact resolve b13e23 b13e2011
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e2011
              have b13e2325 : False := by grind
              exact b13e2325
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
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e27 : x ≠ (M.op x y) := by grind
              have b14e28 : y ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b14e39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b14e16 (k (τ X0) X1)
                   have i₂ := b14e34 X0 X1
                   grind)
                | exact superpose b14e34 b14e16
                | exact resolve b14e16 b14e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e34
              have b14e43 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
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
              have b14e45 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b14e43 X0 X1 x x X4
                   have i₂ := b14e15 X0 X1 x x
                   grind)
                | exact superpose b14e15 b14e43
                | exact resolve b14e43 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e43
              have b14e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X1) (σ X1)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e81 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e18 X0 X0
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e18
                | (have j0 := b14e18 X0 X0
                   have j1 := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X0 X0
                   have r₂ := b14e20 X0 X1
                   grind)
                | (have r₁ := b14e18 X0 X1
                   have r₂ := b14e20 X0 X1
                   grind)
                | exact resolve b14e18 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e84 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e81 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e81
              have b14e104 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e45 X0 X0 x
                   have i₂ := b14e20 X0 X1
                   grind)
                | exact superpose b14e20 b14e45
                | (have j1 := b14e20 X0 X2
                   grind)
                | exact resolve b14e45 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e214 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b14e39 X1 (τ X0)
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e39
                | exact resolve b14e39 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39
              have b14e263 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (k (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e84 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e84 b14e21
                | (have j1 := b14e84 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e21 b14e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e84
              have b14e291 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b14e263 X0 X1
                   have i₂ := b14e21 X1 X1
                   grind)
                | exact superpose b14e21 b14e263
                | (have j0 := b14e263 X0 X1
                   grind)
                | exact resolve b14e263 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e263
              have b14e598 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e45 (σ X1) (σ X1) x
                   have i₂ := b14e76 X0 X1
                   grind)
                | exact superpose b14e76 b14e45
                | (have j1 := b14e76 X2 X0
                   grind)
                | exact resolve b14e45 b14e76
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e76
              have b14e1498 : ∀ X0 X1 X2 X4 : G, (M.op X4 X0) = (k X0 X4) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X4 X0) = X4 := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b14e15 X1 X0 X2 x
                   have i₂ := b14e104 X0 (M.op x X1) X4
                   grind)
                | exact superpose b14e104 b14e15
                | (have j1 := b14e104 X0 X1 X4
                   grind)
                | exact resolve b14e15 b14e104
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e2968 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e291 x y
                   grind)
                | exact superpose b14e291 b14e22
                | (have j1 := b14e291 x y
                   grind)
                | exact resolve b14e22 b14e291
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e291
              have b14e3636 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b14e598 X1 (σ X0) X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e598
              have b14e17897 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (k y X1) = (M.op X1 y) ∨ (M.op X1 y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e28
                   have i₂ := b14e1498 y y X0 X1
                   grind)
                | (have i₁ := b14e28
                   have i₂ := b14e1498 y X0 y X1
                   grind)
                | exact superpose b14e1498 b14e28
                | (have j1 := b14e1498 y X1 x X1
                   grind)
                | (have r₁ := b14e28
                   have r₂ := b14e1498 y X1 x y
                   grind)
                | exact resolve b14e28 b14e1498
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1498
              have b14e17989 : ∀ X1 : G, (k y X1) = (M.op X1 y) ∨ (M.op X1 y) = X1 := by
                intro X1
                first
                | (have j0 := b14e17897 x X1
                   have j1 := b14e104 y X1 X1
                   grind)
                | (have r₁ := b14e17897 X1 X1
                   have r₂ := b14e104 y X1 x
                   grind)
                | (have r₁ := b14e17897 y X1
                   have r₂ := b14e104 y X1 y
                   grind)
                | exact resolve b14e17897 b14e104
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e104 b14e17897
              have b14e58996 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e3636 (τ X1) (τ X0)
                   have i₂ := b14e214 X1 X0
                   grind)
                | exact superpose b14e214 b14e3636
                | (have j0 := b14e3636 (τ X1) (τ X0)
                   grind)
                | exact resolve b14e3636 b14e214
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e214 b14e3636
              have b14e59206 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e58996 X0 X1
                   have i₂ := b14e17 (k X0 X1)
                   grind)
                | exact superpose b14e17 b14e58996
                | (have j0 := b14e58996 X0 X1
                   grind)
                | exact resolve b14e58996 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e58996
              have b14e59267 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e59206 X0 X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e59206
                | (have j0 := b14e59206 X0 X1
                   grind)
                | exact resolve b14e59206 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59206
              have b14e59312 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e59267 X0 X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e59267
                | (have j0 := b14e59267 X0 X1
                   grind)
                | exact resolve b14e59267 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59267
              have b14e59334 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b14e59312 X0 X1
                   have i₂ := b14e17 X1
                   grind)
                | exact superpose b14e17 b14e59312
                | (have j0 := b14e59312 X0 X1
                   grind)
                | exact resolve b14e59312 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59312
              have b14e59346 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
                intro X0 X1
                first
                | (have i₁ := b14e59334 X0 X1
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e59334
                | (have j0 := b14e59334 X0 X1
                   grind)
                | exact resolve b14e59334 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59334
              have b14e59354 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e59346 X0 X0
                   have i₂ := b14e17 X0
                   grind)
                | exact superpose b14e17 b14e59346
                | (have j0 := b14e59346 X0 X1
                   grind)
                | exact resolve b14e59346 b14e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59346
              have b14e63614 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e2968
                   have i₂ := b14e17989 x
                   grind)
                | exact superpose b14e17989 b14e2968
                | (have j1 := b14e17989 x
                   grind)
                | exact resolve b14e2968 b14e17989
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e2968 b14e17989
              have b14e63644 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
              clear b14e63614
              have b14e63653 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) := by
                first
                | (have r₁ := b14e63644
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e63644 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e63644
              have b14e429779 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b14e18 (σ y) (σ x)
                   have i₂ := b14e63653
                   grind)
                | exact superpose b14e63653 b14e18
                | (have j0 := b14e18 (σ y) (σ x)
                   grind)
                | (have r₁ := b14e18 (σ y) (σ x)
                   have r₂ := b14e63653
                   grind)
                | exact resolve b14e18 b14e63653
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e63653
              have b14e429808 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y y)) := by grind
              clear b14e429779
              have b14e429816 : (σ y) = (σ (k y y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e429808
                   have i₂ := b14e21 y x
                   grind)
                | exact superpose b14e21 b14e429808
                | exact resolve b14e429808 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e429808
              have b14e433094 : (k y y) = (τ (σ y)) ∨ (σ y) = (σ (k y x)) := by
                first
                | (have i₁ := b14e16 (k y y)
                   have i₂ := b14e429816
                   grind)
                | exact superpose b14e429816 b14e16
                | exact resolve b14e16 b14e429816
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e429816
              have b14e433109 : (σ y) = (σ (k y x)) ∨ y = (k y y) := by
                first
                | (have i₁ := b14e433094
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e433094
                | exact resolve b14e433094 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e433094
              have b14e434221 : (k y x) = (τ (σ y)) ∨ y = (k y y) := by
                first
                | (have i₁ := b14e16 (k y x)
                   have i₂ := b14e433109
                   grind)
                | exact superpose b14e433109 b14e16
                | exact resolve b14e16 b14e433109
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e433109
              have b14e434251 : y = (k y y) ∨ y = (k y x) := by
                first
                | (have i₁ := b14e434221
                   have i₂ := b14e16 y
                   grind)
                | exact superpose b14e16 b14e434221
                | exact resolve b14e434221 b14e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e434221
              have b14e436344 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (k y x) := by
                first
                | (have i₁ := b14e59354 y y
                   have i₂ := b14e434251
                   grind)
                | exact superpose b14e434251 b14e59354
                | (have j0 := b14e59354 y y
                   grind)
                | (have r₁ := b14e59354 y y
                   have r₂ := b14e434251
                   grind)
                | (have r₁ := b14e59354 y x
                   have r₂ := b14e434251
                   grind)
                | exact resolve b14e59354 b14e434251
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e434251
              have b14e436345 : y ≠ y ∨ y = (M.op y y) ∨ y = (k y x) := by grind
              clear b14e436344
              have b14e436346 : y = (M.op y y) ∨ y = (k y x) := by grind
              clear b14e436345
              have b14e436362 : y = (k y x) := by
                first
                | (have r₁ := b14e436346
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e436346 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e436346
              have b14e438286 : y ≠ y ∨ y = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b14e59354 y x
                   have i₂ := b14e436362
                   grind)
                | exact superpose b14e436362 b14e59354
                | (have j0 := b14e59354 y x
                   grind)
                | (have r₁ := b14e59354 y x
                   have r₂ := b14e436362
                   grind)
                | exact resolve b14e59354 b14e436362
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e59354 b14e436362
              have b14e438289 : y = (M.op x y) ∨ x = (M.op x y) := by grind
              clear b14e438286
              have b14e438294 : y = (M.op x y) := by
                first
                | (have r₁ := b14e438289
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e438289 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e438289
              have b14e438871 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b14e45 x y x
                   have i₂ := b14e438294
                   grind)
                | exact superpose b14e438294 b14e45
                | exact resolve b14e45 b14e438294
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45 b14e438294
              have b14e439237 : y ≠ y := by
                first
                | (have i₁ := b14e28
                   have i₂ := b14e438871 y
                   grind)
                | exact superpose b14e438871 b14e28
                | (have r₁ := b14e28
                   have r₂ := b14e438871 y
                   grind)
                | exact resolve b14e28 b14e438871
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e438871
              have b14e439331 : False := by grind
              exact b14e439331
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
            have b15e18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b15e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b15e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b15e22 : y ≠ (M.op y x) := by grind
            have b15e23 : x = (M.op x x) := by grind
            have b15e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b15e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
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
              | (have i₁ := b15e14 x X0 X1 x
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e41 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b15e18 x X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e18
              | (have j0 := b15e18 x X0
                 grind)
              | (have r₁ := b15e18 x x
                 have r₂ := b15e23
                 grind)
              | exact resolve b15e18 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e43 : ∀ X0 : G, (k x X0) = X0 ∨ (M.op X0 x) = X0 := by
              intro X0
              first
              | (have j0 := b15e41 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e41
            have b15e46 : ∀ X0 : G, x = (M.op X0 x) := by
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
            have b15e68 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have i₁ := b15e25
                 have i₂ := b15e19 (σ x) X0
                 grind)
              | exact superpose b15e19 b15e25
              | (have j1 := b15e19 (σ x) X0
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) x
                 grind)
              | (have r₁ := b15e25
                 have r₂ := b15e19 (σ x) (σ x)
                 grind)
              | exact resolve b15e25 b15e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e69 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
              intro X0
              first
              | (have j0 := b15e68 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e68
            have b15e79 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e46 y
                 grind)
              | exact superpose b15e46 b15e22
              | exact resolve b15e22 b15e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e193 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = (M.op (τ X0) x) := by
              intro X0
              first
              | (have i₁ := b15e33 X0 x
                 have i₂ := b15e43 (τ X0)
                 grind)
              | exact superpose b15e43 b15e33
              | (have j1 := b15e43 (τ X0)
                 grind)
              | exact resolve b15e33 b15e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e33 b15e43
            have b15e196 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = (M.op (τ X0) x) := by
              intro X0
              first
              | (have i₁ := b15e193 X0
                 have i₂ := b15e16 X0
                 grind)
              | exact superpose b15e16 b15e193
              | (have j0 := b15e193 X0
                 grind)
              | exact resolve b15e193 b15e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e193
            have b15e197 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
              intro X0
              first
              | (have i₁ := b15e196 X0
                 have i₂ := b15e46 (τ X0)
                 grind)
              | exact superpose b15e46 b15e196
              | (have j0 := b15e196 X0
                 grind)
              | exact resolve b15e196 b15e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e46 b15e196
            have b15e338 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
              intro X0
              first
              | (have i₁ := b15e69 X0
                 have i₂ := b15e197 X0
                 grind)
              | exact superpose b15e197 b15e69
              | (have j0 := b15e69 X0
                 have j1 := b15e197 X0
                 grind)
              | exact resolve b15e69 b15e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e69 b15e197
            have b15e346 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
              intro X0
              first
              | (have j0 := b15e338 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e338
            have b15e656 : (σ y) ≠ (σ y) ∨ x = (τ (σ y)) := by
              first
              | (have i₁ := b15e24
                 have i₂ := b15e346 (σ y)
                 grind)
              | exact superpose b15e346 b15e24
              | (have j1 := b15e346 (σ y)
                 grind)
              | (have r₁ := b15e24
                 have r₂ := b15e346 (σ y)
                 grind)
              | exact resolve b15e24 b15e346
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e346
            have b15e682 : x = (τ (σ y)) := by grind
            clear b15e656
            have b15e691 : x = y := by
              first
              | (have i₁ := b15e682
                 have i₂ := b15e15 y
                 grind)
              | exact superpose b15e15 b15e682
              | exact resolve b15e682 b15e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e682
            have b15e695 : False := by grind
            exact b15e695
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b16e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b16e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b16e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e23 : y ≠ (M.op y x) := by grind
              have b16e24 : x = (M.op x x) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b16e21 X1 (τ X0)
                   have i₂ := b16e17 X0
                   grind)
                | exact superpose b16e17 b16e21
                | exact resolve b16e21 b16e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e35 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
                intro X0 X1
                first
                | (have i₁ := b16e15 x X0 X1 x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e42 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b16e35 x x
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e35
                | exact resolve b16e35 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35
              have b16e49 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b16e19 x X0
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x X0
                   grind)
                | (have r₁ := b16e19 x x
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e55 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
                intro X0
                first
                | (have j0 := b16e49 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e49
              have b16e58 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b16e55 X0
                   have i₂ := b16e42 X0
                   grind)
                | exact superpose b16e42 b16e55
                | (have j0 := b16e55 X0
                   grind)
                | exact resolve b16e55 b16e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e55
              have b16e59 : x ≠ y := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e42 y
                   grind)
                | exact superpose b16e42 b16e23
                | exact resolve b16e23 b16e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e42
              have b16e80 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b16e26
                   have i₂ := b16e20 (σ x) X0
                   grind)
                | exact superpose b16e20 b16e26
                | (have j1 := b16e20 (σ x) X0
                   grind)
                | (have r₁ := b16e26
                   have r₂ := b16e20 (σ x) x
                   grind)
                | (have r₁ := b16e26
                   have r₂ := b16e20 (σ x) (σ x)
                   grind)
                | exact resolve b16e26 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e81 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b16e80 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e80
              have b16e172 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b16e34 X0 x
                   have i₂ := b16e58 (τ X0)
                   grind)
                | exact superpose b16e58 b16e34
                | (have j1 := b16e58 (τ X0)
                   grind)
                | exact resolve b16e34 b16e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34 b16e58
              have b16e180 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b16e172 X0
                   have i₂ := b16e17 X0
                   grind)
                | exact superpose b16e17 b16e172
                | (have j0 := b16e172 X0
                   grind)
                | exact resolve b16e172 b16e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e172
              have b16e307 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b16e81 X0
                   have i₂ := b16e180 X0
                   grind)
                | exact superpose b16e180 b16e81
                | (have j0 := b16e81 X0
                   have j1 := b16e180 X0
                   grind)
                | exact resolve b16e81 b16e180
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e81 b16e180
              have b16e315 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have j0 := b16e307 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e307
              have b16e689 : (σ y) ≠ (σ y) ∨ x = (τ (σ y)) := by
                first
                | (have i₁ := b16e25
                   have i₂ := b16e315 (σ y)
                   grind)
                | exact superpose b16e315 b16e25
                | (have j1 := b16e315 (σ y)
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e315 (σ y)
                   grind)
                | exact resolve b16e25 b16e315
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e315
              have b16e712 : x = (τ (σ y)) := by grind
              clear b16e689
              have b16e720 : x = y := by
                first
                | (have i₁ := b16e712
                   have i₂ := b16e16 y
                   grind)
                | exact superpose b16e16 b16e712
                | exact resolve b16e712 b16e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e712
              have b16e723 : False := by grind
              exact b16e723
            · have b17e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b17e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b17e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b17e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op y x) := by grind
              have b17e24 : x = (M.op x x) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
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
              have b17e37 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x X0)) := by
                intro X0 X1
                first
                | (have i₁ := b17e15 x X0 X1 x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e15
                | exact resolve b17e15 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e43 : ∀ X0 : G, x = (M.op X0 x) := by
                intro X0
                first
                | (have i₁ := b17e37 x x
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e37
                | exact resolve b17e37 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e37
              have b17e50 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
                intro X0
                first
                | (have i₁ := b17e19 x X0
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e19
                | (have j0 := b17e19 x X0
                   grind)
                | (have r₁ := b17e19 x x
                   have r₂ := b17e24
                   grind)
                | exact resolve b17e19 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e54 : ∀ X0 : G, (M.op X0 x) = X0 ∨ (k x X0) = X0 := by
                intro X0
                first
                | (have j0 := b17e50 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e50
              have b17e57 : ∀ X0 : G, (k x X0) = X0 ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b17e54 X0
                   have i₂ := b17e43 X0
                   grind)
                | exact superpose b17e43 b17e54
                | (have j0 := b17e54 X0
                   grind)
                | exact resolve b17e54 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e54
              have b17e58 : x ≠ y := by
                first
                | (have i₁ := b17e23
                   have i₂ := b17e43 y
                   grind)
                | exact superpose b17e43 b17e23
                | exact resolve b17e23 b17e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e43
              have b17e78 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b17e26
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | exact superpose b17e20 b17e26
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ x) x
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ x) (σ x)
                   grind)
                | exact resolve b17e26 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e79 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b17e78 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e78
              have b17e131 : ∀ X0 : G, (σ (τ X0)) = (k (σ x) X0) ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b17e32 X0 x
                   have i₂ := b17e57 (τ X0)
                   grind)
                | exact superpose b17e57 b17e32
                | (have j1 := b17e57 (τ X0)
                   grind)
                | exact resolve b17e32 b17e57
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e32 b17e57
              have b17e140 : ∀ X0 : G, (k (σ x) X0) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b17e131 X0
                   have i₂ := b17e17 X0
                   grind)
                | exact superpose b17e17 b17e131
                | (have j0 := b17e131 X0
                   grind)
                | exact resolve b17e131 b17e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e131
              have b17e205 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have i₁ := b17e79 X0
                   have i₂ := b17e140 X0
                   grind)
                | exact superpose b17e140 b17e79
                | (have j0 := b17e79 X0
                   have j1 := b17e140 X0
                   grind)
                | exact resolve b17e79 b17e140
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e79 b17e140
              have b17e212 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (τ X0) = x := by
                intro X0
                first
                | (have j0 := b17e205 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e205
              have b17e386 : (σ y) ≠ (σ y) ∨ x = (τ (σ y)) := by
                first
                | (have i₁ := b17e25
                   have i₂ := b17e212 (σ y)
                   grind)
                | exact superpose b17e212 b17e25
                | (have j1 := b17e212 (σ y)
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e212 (σ y)
                   grind)
                | exact resolve b17e25 b17e212
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e212
              have b17e403 : x = (τ (σ y)) := by grind
              clear b17e386
              have b17e409 : x = y := by
                first
                | (have i₁ := b17e403
                   have i₂ := b17e16 y
                   grind)
                | exact superpose b17e16 b17e403
                | exact resolve b17e403 b17e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e403
              have b17e411 : False := by grind
              exact b17e411
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ (M.op x x) := by grind
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
          have b18e42 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b18e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b18e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e44 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b18e42 X0 X1 x x X4
               have i₂ := b18e13 X0 X1 x x
               grind)
            | exact superpose b18e13 b18e42
            | exact resolve b18e42 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42
          have b18e66 : x = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e36
            | (have j1 := b18e18 x x
               grind)
            | exact resolve b18e36 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e81 : x = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b18e66
               have r₂ := b18e22
               grind)
            | exact resolve b18e66 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e66
          have b18e88 : x = (M.op y x) := by
            first
            | (have r₁ := b18e81
               have r₂ := b18e21
               grind)
            | exact resolve b18e81 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e81
          have b18e101 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b18e44 y x x
               have i₂ := b18e88
               grind)
            | exact superpose b18e88 b18e44
            | exact resolve b18e44 b18e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44 b18e88
          have b18e121 : x ≠ x := by
            first
            | (have i₁ := b18e22
               have i₂ := b18e101 x
               grind)
            | exact superpose b18e101 b18e22
            | (have r₁ := b18e22
               have r₂ := b18e101 x
               grind)
            | exact resolve b18e22 b18e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e101
          have b18e129 : False := by grind
          exact b18e129
        · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ (M.op x x) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b19e26 : y = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b19e29 : (σ x) = (k (σ x) (σ y)) := by grind
            clear b19e28
            have b19e31 : (σ x) = (σ (k x y)) := by
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
            have b19e36 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e31
                 grind)
              | exact superpose b19e31 b19e15
              | exact resolve b19e15 b19e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e37 : x = (k x y) := by
              first
              | (have i₁ := b19e36
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e36
              | exact resolve b19e36 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e36
            have b19e40 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 y X0 X1 y
                 have i₂ := b19e26
                 grind)
              | exact superpose b19e26 b19e14
              | exact resolve b19e14 b19e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e76 : x = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e37
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e37
              | (have j1 := b19e19 x x
                 grind)
              | exact resolve b19e37 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e37
            have b19e91 : x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b19e76
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e76 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e76
            have b19e96 : x = (M.op y x) := by
              first
              | (have r₁ := b19e91
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e91 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e91
            have b19e104 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b19e40 x x
                 have i₂ := b19e96
                 grind)
              | exact superpose b19e96 b19e40
              | exact resolve b19e40 b19e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e40 b19e96
            have b19e126 : x ≠ x := by
              first
              | (have i₁ := b19e23
                 have i₂ := b19e104 x
                 grind)
              | exact superpose b19e104 b19e23
              | (have r₁ := b19e23
                 have r₂ := b19e104 x
                 grind)
              | exact resolve b19e23 b19e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e104
            have b19e134 : False := by grind
            exact b19e134
          · have b20e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y x) := by grind
            have b20e23 : x ≠ (M.op x x) := by grind
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
            have b20e44 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b20e14 X2 (M.op (M.op X3 X0) X1) X4 x
                 have i₂ := b20e14 X0 X1 (M.op x X2) X3
                 grind)
              | exact superpose b20e14 b20e14
              | exact resolve b20e14 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e46 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
              intro X0 X1 X4
              first
              | (have i₁ := b20e44 X0 X1 x x X4
                 have i₂ := b20e14 X0 X1 x x
                 grind)
              | exact superpose b20e14 b20e44
              | exact resolve b20e44 b20e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e44
            have b20e78 : x = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e31
              | (have j1 := b20e19 x x
                 grind)
              | exact resolve b20e31 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e90 : x = (M.op y x) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b20e78
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e78 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e78
            have b20e93 : x = (M.op y x) := by
              first
              | (have r₁ := b20e90
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e90 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90
            have b20e96 : ∀ X0 : G, x = (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b20e46 y x x
                 have i₂ := b20e93
                 grind)
              | exact superpose b20e93 b20e46
              | exact resolve b20e46 b20e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e46 b20e93
            have b20e139 : x ≠ x := by
              first
              | (have i₁ := b20e23
                 have i₂ := b20e96 x
                 grind)
              | exact superpose b20e96 b20e23
              | (have r₁ := b20e23
                 have r₂ := b20e96 x
                 grind)
              | exact resolve b20e23 b20e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e96
            have b20e147 : False := by grind
            exact b20e147
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e23 : x ≠ (M.op x x) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e29 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b21e17 (σ x) (σ x)
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e17
              | (have j0 := b21e17 (σ x) (σ x)
                 grind)
              | (have r₁ := b21e17 (σ x) (σ x)
                 have r₂ := b21e25
                 grind)
              | exact resolve b21e17 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e30 : (σ x) = (k (σ x) (σ x)) := by grind
            clear b21e29
            have b21e32 : (σ x) = (σ (k x x)) := by
              first
              | (have i₁ := b21e30
                 have i₂ := b21e20 x x
                 grind)
              | exact superpose b21e20 b21e30
              | exact resolve b21e30 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30
            have b21e44 : (k x x) = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 (k x x)
                 have i₂ := b21e32
                 grind)
              | exact superpose b21e32 b21e15
              | exact resolve b21e15 b21e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e32
            have b21e45 : x = (k x x) := by
              first
              | (have i₁ := b21e44
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e44
              | exact resolve b21e44 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e44
            have b21e57 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b21e45
                 have i₂ := b21e19 x x
                 grind)
              | exact superpose b21e19 b21e45
              | (have j1 := b21e19 x x
                 grind)
              | exact resolve b21e45 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e45
            have b21e68 : x = (M.op x x) := by grind
            clear b21e57
            have b21e73 : False := by grind
            exact b21e73
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : x ≠ (M.op x x) := by grind
              have b22e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b22e18 (σ x) (σ x)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e18
                | (have j0 := b22e18 (σ x) (σ x)
                   grind)
                | (have r₁ := b22e18 (σ x) (σ x)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e18 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e31 : (σ x) = (k (σ x) (σ x)) := by grind
              clear b22e30
              have b22e33 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b22e31
                   have i₂ := b22e21 x x
                   grind)
                | exact superpose b22e21 b22e31
                | exact resolve b22e31 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e31
              have b22e38 : (k x x) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x x)
                   have i₂ := b22e33
                   grind)
                | exact superpose b22e33 b22e16
                | exact resolve b22e16 b22e33
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e33
              have b22e39 : x = (k x x) := by
                first
                | (have i₁ := b22e38
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e38
                | exact resolve b22e38 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e38
              have b22e70 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b22e39
                   have i₂ := b22e20 x x
                   grind)
                | exact superpose b22e20 b22e39
                | (have j1 := b22e20 x x
                   grind)
                | exact resolve b22e39 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e39
              have b22e82 : x = (M.op x x) := by grind
              clear b22e70
              have b22e88 : False := by grind
              exact b22e88
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : x ≠ (M.op x x) := by grind
              have b23e26 : (σ x) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e29 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
                first
                | (have i₁ := b23e18 (σ x) (σ x)
                   have i₂ := b23e26
                   grind)
                | exact superpose b23e26 b23e18
                | (have j0 := b23e18 (σ x) (σ x)
                   grind)
                | (have r₁ := b23e18 (σ x) (σ x)
                   have r₂ := b23e26
                   grind)
                | exact resolve b23e18 b23e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b23e30 : (σ x) = (k (σ x) (σ x)) := by grind
              clear b23e29
              have b23e31 : (σ x) = (σ (k x x)) := by
                first
                | (have i₁ := b23e30
                   have i₂ := b23e21 x x
                   grind)
                | exact superpose b23e21 b23e30
                | exact resolve b23e30 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30
              have b23e36 : (k x x) = (τ (σ x)) := by
                first
                | (have i₁ := b23e16 (k x x)
                   have i₂ := b23e31
                   grind)
                | exact superpose b23e31 b23e16
                | exact resolve b23e16 b23e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e31
              have b23e37 : x = (k x x) := by
                first
                | (have i₁ := b23e36
                   have i₂ := b23e16 x
                   grind)
                | exact superpose b23e16 b23e36
                | exact resolve b23e36 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e36
              have b23e78 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
                first
                | (have i₁ := b23e37
                   have i₂ := b23e20 x x
                   grind)
                | exact superpose b23e20 b23e37
                | (have j1 := b23e20 x x
                   grind)
                | exact resolve b23e37 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e37
              have b23e89 : x = (M.op x x) := by grind
              clear b23e78
              have b23e93 : False := by grind
              exact b23e93
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
              intro X0 X1 X2 X3
              grind
            have b24e23 : x ≠ (M.op x x) := by grind
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
            have b24e52 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) := by
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
            have b24e98 : ∀ X0 : G, x ≠ (M.op X0 x) := by
              intro X0
              first
              | (have i₁ := b24e23
                 have i₂ := b24e52 x X0
                 grind)
              | (have i₁ := b24e23
                 have i₂ := b24e52 X0 x
                 grind)
              | exact superpose b24e52 b24e23
              | exact resolve b24e23 b24e52
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e52
            have b24e109 : ∀ X0 : G, x = (M.op X0 x) := by
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
            have b24e131 : False := by grind
            exact b24e131
          · rcases eq_or_ne (M.op y y) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
                intro X0 X1 X2 X3
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e28 : y = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e29 : y ≠ y ∨ y = (k y y) := by
                first
                | (have i₁ := b25e18 y y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e18
                | (have j0 := b25e18 y y
                   grind)
                | (have r₁ := b25e18 y y
                   have r₂ := b25e28
                   grind)
                | exact resolve b25e18 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e30 : y = (k y y) := by grind
              clear b25e29
              have b25e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
                intro X0 X1
                first
                | (have i₁ := b25e15 y X0 X1 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
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
              have b25e41 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
                intro X0 X1 X4
                first
                | (have i₁ := b25e39 X0 X1 x x X4
                   have i₂ := b25e15 X0 X1 x x
                   grind)
                | exact superpose b25e15 b25e39
                | exact resolve b25e39 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39
              have b25e43 : ∀ X0 : G, y = (M.op X0 y) := by
                intro X0
                first
                | (have i₁ := b25e37 y x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37
              have b25e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X1)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e541 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e70 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e70
              have b25e543 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e541 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e541
              have b25e1077 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
                first
                | (have i₁ := b25e543 y
                   have i₂ := b25e30
                   grind)
                | exact superpose b25e30 b25e543
                | (have j0 := b25e543 y
                   grind)
                | exact resolve b25e543 b25e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e30 b25e543
              have b25e1082 : (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b25e1077
              have b25e1283 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
                intro X0
                first
                | (have i₁ := b25e41 (σ y) (σ y) x
                   have i₂ := b25e1082
                   grind)
                | exact superpose b25e1082 b25e41
                | exact resolve b25e41 b25e1082
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e41 b25e1082
              have b25e1339 : (σ (M.op x y)) ≠ (σ y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e1283 (σ x)
                   grind)
                | exact superpose b25e1283 b25e22
                | exact resolve b25e22 b25e1283
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1283
              have b25e1370 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b25e1339
                   have i₂ := b25e43 x
                   grind)
                | exact superpose b25e43 b25e1339
                | exact resolve b25e1339 b25e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43 b25e1339
              have b25e1371 : False := by grind
              exact b25e1371
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
              have b26e19 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
              have b26e27 : x ≠ (M.op x y) := by grind
              have b26e28 : y ≠ (M.op y y) := by grind
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
              have b26e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 (τ X0)
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
              have b26e33 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ X2 ∨ (M.op (M.op X3 X0) X1) = (k (M.op (M.op X3 X0) X1) X2) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e18 (M.op (M.op X3 X0) X1) X2
                   have i₂ := b26e15 X0 X1 X2 X3
                   grind)
                | exact superpose b26e15 b26e18
                | (have j0 := b26e18 (M.op (M.op X3 X0) X1) X2
                   grind)
                | (have r₁ := b26e18 (M.op (M.op X3 X0) X1) (M.op X0 X1)
                   have r₂ := b26e15 X0 X1 (M.op X0 X1) X3
                   grind)
                | exact resolve b26e18 b26e15
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
              have b26e45 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X2 (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e19 (M.op X0 X1) X2
                   have i₂ := b26e34 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e34 b26e19
                | (have j0 := b26e19 (M.op X0 X1) X2
                   grind)
                | (have r₁ := b26e19 (M.op X0 X1) X1
                   have r₂ := b26e34 X0 X1 (M.op X0 X1)
                   grind)
                | exact resolve b26e19 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e46 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = X2 ∨ (k (M.op X0 X1) X2) = X2 := by
                intro X0 X1 X2
                first
                | (have j0 := b26e45 X0 X1 X2
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e45
              have b26e47 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = X2 ∨ (M.op X0 X1) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e46 X0 X1 X2
                   have i₂ := b26e34 X0 X1 X2
                   grind)
                | exact superpose b26e34 b26e46
                | (have j0 := b26e46 X0 X1 X2
                   grind)
                | exact resolve b26e46 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e46
              have b26e58 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (k X1 (M.op X2 X0)) = X1 := by
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
              have b26e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X1)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e70 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X0 X2) ∨ (M.op X1 X0) = X0 ∨ (M.op X2 X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 X0 X0 x
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e34
                | (have j1 := b26e20 X0 X2
                   grind)
                | exact resolve b26e34 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e72 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e18 X0 X0
                   have i₂ := b26e20 X0 X1
                   grind)
                | exact superpose b26e20 b26e18
                | (have j0 := b26e18 X0 X0
                   have j1 := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X0
                   have r₂ := b26e20 X0 X1
                   grind)
                | (have r₁ := b26e18 X0 X1
                   have r₂ := b26e20 X0 X1
                   grind)
                | exact resolve b26e18 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e76 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have i₁ := b26e26
                   have i₂ := b26e20 (σ x) X0
                   grind)
                | exact superpose b26e20 b26e26
                | (have j1 := b26e20 (σ x) X0
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) x
                   grind)
                | (have r₁ := b26e26
                   have r₂ := b26e20 (σ x) (σ x)
                   grind)
                | exact resolve b26e26 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e77 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
                intro X0
                first
                | (have j0 := b26e76 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e76
              have b26e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e72 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e72
              have b26e85 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k (τ X0) X1)
                   have i₂ := b26e29 X0 X1
                   grind)
                | exact superpose b26e29 b26e16
                | exact resolve b26e16 b26e29
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (k X0 (τ X1))
                   have i₂ := b26e30 X1 X0
                   grind)
                | exact superpose b26e30 b26e16
                | exact resolve b26e16 b26e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e95 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
                intro X0 X1
                first
                | (have i₁ := b26e85 X1 (τ X0)
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e85
                | exact resolve b26e85 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e85
              have b26e142 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
                intro X0
                first
                | (have i₁ := b26e21 x X0
                   have i₂ := b26e77 (σ X0)
                   grind)
                | exact superpose b26e77 b26e21
                | (have j1 := b26e77 (σ X0)
                   grind)
                | exact resolve b26e21 b26e77
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e77
              have b26e166 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (k (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e78 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e78 b26e21
                | (have j1 := b26e78 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e78
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e78
              have b26e193 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b26e166 X0 X1
                   have i₂ := b26e21 X1 X1
                   grind)
                | exact superpose b26e21 b26e166
                | (have j0 := b26e166 X0 X1
                   grind)
                | exact resolve b26e166 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e166
              have b26e206 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (M.op X1 X2)) X0) ∨ (τ X0) = (M.op X1 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e30 X0 (M.op X1 X2)
                   have i₂ := b26e47 X1 X2 (τ X0)
                   grind)
                | exact superpose b26e47 b26e30
                | (have j1 := b26e47 X1 X2 (τ X0)
                   grind)
                | exact resolve b26e30 b26e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e211 : ∀ X0 X1 X2 : G, (k (σ (M.op X1 X2)) X0) = X0 ∨ (τ X0) = (M.op X1 X2) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e206 X0 X1 X2
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e206
                | (have j0 := b26e206 X0 X1 X2
                   grind)
                | exact resolve b26e206 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e206
              have b26e222 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op (M.op X0 X1) X2) (M.op X1 X2)) := by
                intro X0 X1 X2
                first
                | (have j0 := b26e33 X1 X2 (M.op X1 X2) X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e33
              have b26e223 : ∀ X1 X2 : G, (M.op X1 X2) = (k (M.op X1 X2) (M.op X1 X2)) := by
                intro X1 X2
                first
                | (have i₁ := b26e222 x X1 X2
                   have i₂ := b26e39 x X1 X2
                   grind)
                | exact superpose b26e39 b26e222
                | exact resolve b26e222 b26e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e39 b26e222
              have b26e330 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X0)) = (σ (k X0 X2)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 (σ X1) (σ X1) x
                   have i₂ := b26e68 X0 X1
                   grind)
                | exact superpose b26e68 b26e34
                | (have j1 := b26e68 X2 X0
                   grind)
                | exact resolve b26e34 b26e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e335 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e68 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e68
              have b26e337 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b26e335 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e335
              have b26e369 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
                intro X0
                first
                | (have j0 := b26e58 X0 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e58
              have b26e429 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
                intro X0
                first
                | (have i₁ := b26e92 X0 (M.op (σ X0) (σ X0))
                   have i₂ := b26e369 (σ X0)
                   grind)
                | exact superpose b26e369 b26e92
                | exact resolve b26e92 b26e369
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e92
              have b26e431 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
                intro X0
                first
                | (have i₁ := b26e29 X0 (M.op (τ X0) (τ X0))
                   have i₂ := b26e369 (τ X0)
                   grind)
                | exact superpose b26e369 b26e29
                | exact resolve b26e29 b26e369
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e29
              have b26e435 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e431 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e431
                | exact resolve b26e431 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e431
              have b26e436 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
                intro X0
                first
                | (have i₁ := b26e429 X0
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e429
                | exact resolve b26e429 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e429
              have b26e498 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) ∨ (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have i₁ := b26e47 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   have i₂ := b26e435 (M.op X0 X1)
                   grind)
                | exact superpose b26e435 b26e47
                | (have j0 := b26e47 X0 X1 (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))))
                   grind)
                | exact resolve b26e47 b26e435
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e47 b26e435
              have b26e504 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))) := by
                intro X0 X1
                first
                | (have j0 := b26e498 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e498
              have b26e734 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e337 (M.op X0 X1)
                   have i₂ := b26e223 X0 X1
                   grind)
                | exact superpose b26e223 b26e337
                | (have j0 := b26e337 (M.op X0 X1)
                   grind)
                | exact resolve b26e337 b26e223
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e223 b26e337
              have b26e740 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have j0 := b26e734 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e734
              have b26e824 : ∀ X0 X1 X2 X4 : G, (M.op X4 X0) = (k X0 X4) ∨ (M.op X1 X0) = (M.op X2 X0) ∨ (M.op X4 X0) = X4 := by
                intro X0 X1 X2 X4
                first
                | (have i₁ := b26e15 X1 X0 X2 x
                   have i₂ := b26e70 X0 (M.op x X1) X4
                   grind)
                | exact superpose b26e70 b26e15
                | (have j1 := b26e70 X0 X1 X4
                   grind)
                | exact resolve b26e15 b26e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e904 : x = (k x (τ (σ (k x x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b26e436 x
                   have i₂ := b26e142 x
                   grind)
                | exact superpose b26e142 b26e436
                | (have j1 := b26e142 x
                   grind)
                | exact resolve b26e436 b26e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e436
              have b26e906 : (σ x) = (k (σ x) (σ (k x x))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b26e369 (σ x)
                   have i₂ := b26e142 x
                   grind)
                | exact superpose b26e142 b26e369
                | (have j1 := b26e142 x
                   grind)
                | exact resolve b26e369 b26e142
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e369
              have b26e926 : (σ x) = (k (σ x) (σ (k x x))) := by
                first
                | (have r₁ := b26e906
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e906 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e906
              have b26e928 : x = (k x (τ (σ (k x x)))) := by
                first
                | (have r₁ := b26e904
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e904 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e904
              have b26e930 : (σ x) = (σ (k x (k x x))) := by
                first
                | (have i₁ := b26e926
                   have i₂ := b26e21 x (k x x)
                   grind)
                | exact superpose b26e21 b26e926
                | exact resolve b26e926 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e926
              have b26e931 : x = (k x (k x x)) := by
                first
                | (have i₁ := b26e928
                   have i₂ := b26e16 (k x x)
                   grind)
                | exact superpose b26e16 b26e928
                | exact resolve b26e928 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e928
              have b26e1006 : (M.op (σ x) (σ x)) = (σ (k x (k x (k x x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
                first
                | (have i₁ := b26e142 (k x (k x x))
                   have i₂ := b26e930
                   grind)
                | exact superpose b26e930 b26e142
                | (have j0 := b26e142 x
                   grind)
                | exact resolve b26e142 b26e930
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e142 b26e930
              have b26e1012 : (M.op (σ x) (σ x)) = (σ (k x (k x (k x x)))) := by
                first
                | (have r₁ := b26e1006
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e1006 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1006
              have b26e1034 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
                first
                | (have i₁ := b26e1012
                   have i₂ := b26e931
                   grind)
                | exact superpose b26e931 b26e1012
                | exact resolve b26e1012 b26e931
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e931 b26e1012
              have b26e1072 : (σ x) ≠ (σ (k x x)) := by
                first
                | (have i₁ := b26e26
                   have i₂ := b26e1034
                   grind)
                | exact superpose b26e1034 b26e26
                | exact resolve b26e26 b26e1034
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1034
              have b26e2109 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e193 x y
                   grind)
                | exact superpose b26e193 b26e22
                | (have j1 := b26e193 x y
                   grind)
                | exact resolve b26e22 b26e193
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e193
              have b26e2621 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have j0 := b26e330 X1 (σ X0) X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e330
              have b26e5159 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (σ (M.op X1 X2))) X0) ∨ (M.op X1 X2) = (τ (τ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e30 X0 (σ (M.op X1 X2))
                   have i₂ := b26e211 (τ X0) X1 X2
                   grind)
                | exact superpose b26e211 b26e30
                | (have j1 := b26e211 (τ X0) X1 X2
                   grind)
                | exact resolve b26e30 b26e211
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30 b26e211
              have b26e5188 : ∀ X0 X1 X2 : G, (k (σ (σ (M.op X1 X2))) X0) = X0 ∨ (M.op X1 X2) = (τ (τ X0)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e5159 X0 X1 X2
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e5159
                | (have j0 := b26e5159 X0 X1 X2
                   grind)
                | exact resolve b26e5159 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5159
              have b26e5570 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op X2 (σ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 (σ (M.op X0 X1)) (σ (M.op X0 X1)) x
                   have i₂ := b26e740 X0 X1
                   grind)
                | exact superpose b26e740 b26e34
                | exact resolve b26e34 b26e740
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e740
              have b26e5966 : ∀ X0 X1 X3 : G, (σ (σ (M.op X0 X1))) = (M.op X3 (σ (σ (M.op X0 X1)))) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e5570 x (σ (M.op X0 X1)) x
                   have i₂ := b26e5570 X0 X1 x
                   grind)
                | exact superpose b26e5570 b26e5570
                | exact resolve b26e5570 b26e5570
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5570
              have b26e7900 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b26e16 (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1)))
                   have i₂ := b26e504 X0 X1
                   grind)
                | exact superpose b26e504 b26e16
                | exact resolve b26e16 b26e504
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e504
              have b26e9279 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op X2 (τ (M.op X0 X1))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e34 (τ (M.op X0 X1)) (τ (M.op X0 X1)) x
                   have i₂ := b26e7900 X0 X1
                   grind)
                | exact superpose b26e7900 b26e34
                | exact resolve b26e34 b26e7900
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34 b26e7900
              have b26e9503 : ∀ X0 X1 X3 : G, (τ (τ (M.op X0 X1))) = (M.op X3 (τ (τ (M.op X0 X1)))) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e9279 x (τ (M.op X0 X1)) x
                   have i₂ := b26e9279 X0 X1 x
                   grind)
                | exact superpose b26e9279 b26e9279
                | exact resolve b26e9279 b26e9279
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9279
              have b26e10255 : ∀ X0 X1 : G, y ≠ (M.op X0 y) ∨ (M.op X1 y) = (k y X1) ∨ (M.op X1 y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e28
                   have i₂ := b26e824 y y X0 X1
                   grind)
                | (have i₁ := b26e28
                   have i₂ := b26e824 y X0 y X1
                   grind)
                | exact superpose b26e824 b26e28
                | (have j1 := b26e824 y X1 x X1
                   grind)
                | (have r₁ := b26e28
                   have r₂ := b26e824 y X1 x y
                   grind)
                | exact resolve b26e28 b26e824
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e824
              have b26e10298 : ∀ X1 : G, (M.op X1 y) = (k y X1) ∨ (M.op X1 y) = X1 := by
                intro X1
                first
                | (have j0 := b26e10255 x X1
                   have j1 := b26e70 y X1 X1
                   grind)
                | (have r₁ := b26e10255 X1 X1
                   have r₂ := b26e70 y X1 x
                   grind)
                | (have r₁ := b26e10255 y X1
                   have r₂ := b26e70 y X1 y
                   grind)
                | exact resolve b26e10255 b26e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e70 b26e10255
              have b26e19370 : ∀ X0 X1 X3 : G, (k (σ (σ (τ (τ (M.op X0 X1))))) X3) = X3 ∨ (τ (τ (M.op X0 X1))) = (τ (τ X3)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e5188 X0 X3 (τ (τ (M.op X0 X1)))
                   have i₂ := b26e9503 X0 X1 X3
                   grind)
                | exact superpose b26e9503 b26e5188
                | exact resolve b26e5188 b26e9503
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5188
              have b26e19565 : ∀ X0 X1 X3 : G, (k (σ (τ (M.op X0 X1))) X3) = X3 ∨ (τ (τ (M.op X0 X1))) = (τ (τ X3)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e19370 X0 X1 X3
                   have i₂ := b26e17 (τ (M.op X0 X1))
                   grind)
                | exact superpose b26e17 b26e19370
                | (have j0 := b26e19370 X0 X1 X3
                   grind)
                | exact resolve b26e19370 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19370
              have b26e19611 : ∀ X0 X1 X3 : G, (k (M.op X0 X1) X3) = X3 ∨ (τ (τ (M.op X0 X1))) = (τ (τ X3)) := by
                intro X0 X1 X3
                first
                | (have i₁ := b26e19565 X0 X1 X3
                   have i₂ := b26e17 (M.op X0 X1)
                   grind)
                | exact superpose b26e17 b26e19565
                | (have j0 := b26e19565 X0 X1 X3
                   grind)
                | exact resolve b26e19565 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e19565
              have b26e36484 : ∀ X0 X1 X2 X3 : G, (τ (τ X0)) = (M.op X3 (τ (τ X0))) ∨ (k (M.op X1 X2) X0) = X0 := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b26e9503 X0 X1 X3
                   have i₂ := b26e19611 X0 X1 X3
                   grind)
                | (have i₁ := b26e9503 X0 X1 X3
                   have i₂ := b26e19611 X0 X1 (M.op X0 X1)
                   grind)
                | exact superpose b26e19611 b26e9503
                | (have j1 := b26e19611 X1 X2 X0
                   grind)
                | exact resolve b26e9503 b26e19611
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e9503 b26e19611
              have b26e38378 : ∀ X0 X2 X3 X4 : G, (σ (σ (τ (τ X0)))) = (M.op X2 (σ (σ (τ (τ X0))))) ∨ (k (M.op X3 X4) X0) = X0 := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b26e5966 X3 (τ (τ X0)) X3
                   have i₂ := b26e36484 X0 x X2 X3
                   grind)
                | exact superpose b26e36484 b26e5966
                | (have j1 := b26e36484 X0 X3 X4 X3
                   grind)
                | exact resolve b26e5966 b26e36484
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e5966 b26e36484
              have b26e38579 : ∀ X0 X2 X3 X4 : G, (σ (τ X0)) = (M.op X2 (σ (τ X0))) ∨ (k (M.op X3 X4) X0) = X0 := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b26e38378 X0 X2 X3 X4
                   have i₂ := b26e17 (τ X0)
                   grind)
                | exact superpose b26e17 b26e38378
                | (have j0 := b26e38378 X0 X2 X3 X4
                   grind)
                | exact resolve b26e38378 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38378
              have b26e38648 : ∀ X0 X2 X3 X4 : G, (M.op X2 X0) = X0 ∨ (k (M.op X3 X4) X0) = X0 := by
                intro X0 X2 X3 X4
                first
                | (have i₁ := b26e38579 X0 X2 X3 X4
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e38579
                | (have j0 := b26e38579 X0 X2 X3 X4
                   grind)
                | exact resolve b26e38579 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38579
              have b26e39096 : ∀ X0 X1 X2 X4 X5 : G, (M.op X1 X0) = (M.op X2 X0) ∨ (k (M.op X4 X5) X0) = X0 := by
                intro X0 X1 X2 X4 X5
                first
                | (have i₁ := b26e15 X1 X0 X2 x
                   have i₂ := b26e38648 X0 (M.op x X1) X4 X5
                   grind)
                | exact superpose b26e38648 b26e15
                | (have j1 := b26e38648 X0 X2 X4 X5
                   grind)
                | exact resolve b26e15 b26e38648
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e44437 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e2621 (τ X1) (τ X0)
                   have i₂ := b26e95 X1 X0
                   grind)
                | exact superpose b26e95 b26e2621
                | (have j0 := b26e2621 (τ X1) (τ X0)
                   grind)
                | exact resolve b26e2621 b26e95
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e95 b26e2621
              have b26e44598 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e44437 X0 X1
                   have i₂ := b26e17 (k X0 X1)
                   grind)
                | exact superpose b26e17 b26e44437
                | (have j0 := b26e44437 X0 X1
                   grind)
                | exact resolve b26e44437 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44437
              have b26e44636 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e44598 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e44598
                | (have j0 := b26e44598 X0 X1
                   grind)
                | exact resolve b26e44598 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44598
              have b26e44663 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e44636 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e44636
                | (have j0 := b26e44636 X0 X1
                   grind)
                | exact resolve b26e44636 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44636
              have b26e44678 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
                intro X0 X1
                first
                | (have i₁ := b26e44663 X0 X1
                   have i₂ := b26e17 X1
                   grind)
                | exact superpose b26e17 b26e44663
                | (have j0 := b26e44663 X0 X1
                   grind)
                | exact resolve b26e44663 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44663
              have b26e44688 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e44678 X0 X1
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e44678
                | (have j0 := b26e44678 X0 X1
                   grind)
                | exact resolve b26e44678 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44678
              have b26e44694 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e44688 X0 X0
                   have i₂ := b26e17 X0
                   grind)
                | exact superpose b26e17 b26e44688
                | (have j0 := b26e44688 X0 X1
                   grind)
                | exact resolve b26e44688 b26e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44688
              have b26e50555 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e2109
                   have i₂ := b26e10298 x
                   grind)
                | exact superpose b26e10298 b26e2109
                | (have j1 := b26e10298 x
                   grind)
                | exact resolve b26e2109 b26e10298
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2109 b26e10298
              have b26e50572 : (σ y) = (σ (k y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
              clear b26e50555
              have b26e50580 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y y)) := by
                first
                | (have r₁ := b26e50572
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e50572 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e50572
              have b26e51135 : ∀ X0 X1 X2 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (σ x) = (k (M.op X1 X2) (σ x)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e26
                   have i₂ := b26e39096 (σ x) (σ x) X0 X1 X2
                   grind)
                | (have i₁ := b26e26
                   have i₂ := b26e39096 (σ x) X0 (σ x) X1 X2
                   grind)
                | exact superpose b26e39096 b26e26
                | (have j1 := b26e39096 (σ x) X1 X2 X1 X2
                   grind)
                | exact resolve b26e26 b26e39096
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e39096
              have b26e51356 : ∀ X1 X2 : G, (σ x) = (k (M.op X1 X2) (σ x)) := by
                intro X1 X2
                first
                | (have j0 := b26e51135 x X1 X2
                   have j1 := b26e38648 (σ x) X2 X1 X2
                   grind)
                | (have r₁ := b26e51135 X2 X1 X2
                   have r₂ := b26e38648 (σ x) X2 x x
                   grind)
                | exact resolve b26e51135 b26e38648
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e38648 b26e51135
              have b26e155090 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b26e51356 (σ x) (σ y)
                   have i₂ := b26e50580
                   grind)
                | exact superpose b26e50580 b26e51356
                | exact resolve b26e51356 b26e50580
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e50580 b26e51356
              have b26e155266 : (σ x) = (σ (k x x)) ∨ (σ y) = (σ (k y y)) := by
                first
                | (have i₁ := b26e155090
                   have i₂ := b26e21 x x
                   grind)
                | exact superpose b26e21 b26e155090
                | exact resolve b26e155090 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e155090
              have b26e155304 : (σ y) = (σ (k y y)) := by
                first
                | (have r₁ := b26e155266
                   have r₂ := b26e1072
                   grind)
                | exact resolve b26e155266 b26e1072
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e1072 b26e155266
              have b26e156300 : (k y y) = (τ (σ y)) := by
                first
                | (have i₁ := b26e16 (k y y)
                   have i₂ := b26e155304
                   grind)
                | exact superpose b26e155304 b26e16
                | exact resolve b26e16 b26e155304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e155304
              have b26e156362 : y = (k y y) := by
                first
                | (have i₁ := b26e156300
                   have i₂ := b26e16 y
                   grind)
                | exact superpose b26e16 b26e156300
                | exact resolve b26e156300 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e156300
              have b26e157078 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) := by
                first
                | (have i₁ := b26e44694 y y
                   have i₂ := b26e156362
                   grind)
                | exact superpose b26e156362 b26e44694
                | (have j0 := b26e44694 y y
                   grind)
                | (have r₁ := b26e44694 y y
                   have r₂ := b26e156362
                   grind)
                | exact resolve b26e44694 b26e156362
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e44694 b26e156362
              have b26e157079 : y ≠ y ∨ y = (M.op y y) := by grind
              clear b26e157078
              have b26e157080 : y = (M.op y y) := by grind
              clear b26e157079
              have b26e157110 : False := by grind
              exact b26e157110

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then Y else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_y_x_pxy_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = b :=
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
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y y) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (σ x) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X0 X1 (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 (M.op (M.op X3 X0) X1) X4 x
           have i₂ := b0e11 X0 X1 (M.op x X2) X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e35 X0 X1 x x X4
           have i₂ := b0e11 X0 X1 x x
           grind)
        | exact superpose b0e11 b0e35
        | exact resolve b0e35 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e74 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e32 X0 x
           have i₂ := b0e37 x X0 x
           grind)
        | exact superpose b0e37 b0e32
        | exact resolve b0e32 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e216 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e37 (σ x) X0 x
           have i₂ := b0e33 X0 x
           grind)
        | exact superpose b0e33 b0e37
        | exact resolve b0e37 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e37
      have b0e655 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e216 (σ y)
           grind)
        | exact superpose b0e216 b0e18
        | exact resolve b0e18 b0e216
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e216
      have b0e682 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e655
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e655
        | exact resolve b0e655 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e655
      have b0e689 : (σ x) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e682
           have i₂ := b0e74 y
           grind)
        | exact superpose b0e74 b0e682
        | exact resolve b0e682 b0e74
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e74 b0e682
      have b0e691 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e689
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e689
        | exact resolve b0e689 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e689
      have b0e692 : False := by grind
      exact b0e692
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b1e25 : y = (k x y) := by grind
        have b1e54 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        have b1e66 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e54
             have r₂ := b1e21
             grind)
          | exact resolve b1e54 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e69 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e66
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e66
          | exact resolve b1e66 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66
        have b1e70 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e69
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e69
          | exact resolve b1e69 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e69
        have b1e71 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e19
          | exact resolve b1e19 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e72 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e22
          | exact resolve b1e22 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e75 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e70
             grind)
          | exact superpose b1e70 b1e13
          | exact resolve b1e13 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e76 : x = y := by
          first
          | (have i₁ := b1e75
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e75
          | exact resolve b1e75 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e75
        have b1e79 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e71
             have i₂ := b1e72
             grind)
          | exact superpose b1e72 b1e71
          | exact resolve b1e71 b1e72
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71 b1e72
        have b1e80 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e79
             have i₂ := b1e76
             grind)
          | exact superpose b1e76 b1e79
          | exact resolve b1e79 b1e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e76 b1e79
        have b1e81 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e80
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e80
          | exact resolve b1e80 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e80
        have b1e82 : False := by grind
        exact b1e82
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        have b2e25 : y = (k x y) := by grind
        have b2e28 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 y X0 X1 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X2 (M.op (M.op X3 X0) X1) X4 x
             have i₂ := b2e12 X0 X1 (M.op x X2) X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (k (M.op X0 X1) (M.op (M.op X2 X0) X1)) := by
          intro X0 X1 X2
          grind
        have b2e32 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b2e30 X0 X1 x x X4
             have i₂ := b2e12 X0 X1 x x
             grind)
          | exact superpose b2e12 b2e30
          | exact resolve b2e30 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e66 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e28 X0 x
             have i₂ := b2e32 x X0 x
             grind)
          | exact superpose b2e32 b2e28
          | exact resolve b2e28 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e98 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e1227 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e98 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e1228 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1227
             have r₂ := b2e22
             grind)
          | exact resolve b2e1227 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1227
        have b2e1229 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1228
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1228
          | exact resolve b2e1228 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1228
        have b2e1230 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1229
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e1229
          | exact resolve b2e1229 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e1229
        have b2e1231 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e1230
             grind)
          | exact superpose b2e1230 b2e19
          | exact resolve b2e19 b2e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1233 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (σ y) (M.op (M.op X0 (σ x)) (σ y))) := by
          intro X0
          first
          | (have i₁ := b2e31 (σ x) (σ y) X0
             have i₂ := b2e1230
             grind)
          | exact superpose b2e1230 b2e31
          | exact resolve b2e31 b2e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e1235 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e32 (σ x) (σ y) x
             have i₂ := b2e1230
             grind)
          | exact superpose b2e1230 b2e32
          | exact resolve b2e32 b2e1230
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e1230
        have b2e1237 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1233 x
             have i₂ := b2e1235 (M.op x (σ x))
             grind)
          | exact superpose b2e1235 b2e1233
          | exact resolve b2e1233 b2e1235
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1233 b2e1235
        have b2e1238 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1231
             have i₂ := b2e66 y
             grind)
          | exact superpose b2e66 b2e1231
          | exact resolve b2e1231 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66 b2e1231
        have b2e1239 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b2e1237
             have i₂ := b2e18 y y
             grind)
          | exact superpose b2e18 b2e1237
          | exact resolve b2e1237 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1237
        have b2e1240 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e1238
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1238
          | exact resolve b2e1238 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1238
        have b2e1312 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1239
             have i₂ := b2e17 y y
             grind)
          | exact superpose b2e17 b2e1239
          | (have j1 := b2e17 y y
             grind)
          | exact resolve b2e1239 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1239
        have b2e1322 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b2e1312
        have b2e1332 : (σ x) = (σ y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e1322
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1322
          | exact resolve b2e1322 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1322
        have b2e1333 : y = (M.op y y) := by
          first
          | (have r₁ := b2e1332
             have r₂ := b2e1240
             grind)
          | exact resolve b2e1332 b2e1240
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1332
        have b2e1994 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e1333
             grind)
          | exact superpose b2e1333 b2e20
          | exact resolve b2e20 b2e1333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1333
        have b2e2513 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1240
             have i₂ := b2e1994
             grind)
          | exact superpose b2e1994 b2e1240
          | exact resolve b2e1240 b2e1994
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1240 b2e1994
        have b2e2514 : False := by grind
        exact b2e2514
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
        have b3e27 : (σ y) = (σ (k x y)) := by
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
        have b3e32 : (k x y) = (τ (σ y)) := by
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
        have b3e33 : y = (k x y) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e32
          | exact resolve b3e32 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e55 : x = (M.op y y) ∨ x = (k x y) := by grind
        have b3e65 : x = (k x y) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e20
             grind)
          | exact resolve b3e55 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e69 : x = y := by
          first
          | (have i₁ := b3e65
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e65
          | exact resolve b3e65 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e65
        have b3e72 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e69
             grind)
          | exact superpose b3e69 b3e19
          | exact resolve b3e19 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e69
             grind)
          | exact superpose b3e69 b3e21
          | exact resolve b3e21 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e76 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e72
             have i₂ := b3e75
             grind)
          | exact superpose b3e75 b3e72
          | exact resolve b3e72 b3e75
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72 b3e75
        have b3e77 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e76
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e76
          | exact resolve b3e76 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e76
        have b3e78 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e69
             grind)
          | exact superpose b3e69 b3e77
          | exact resolve b3e77 b3e69
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69 b3e77
        have b3e79 : False := by grind
        exact b3e79
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b4e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b4e39 X0 X1 x x X4
               have i₂ := b4e13 X0 X1 x x
               grind)
            | exact superpose b4e13 b4e39
            | exact resolve b4e39 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e130 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e41 (σ x) (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e131 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e41 x x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e41
            | exact resolve b4e41 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e389 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e130 (σ x)
               grind)
            | exact superpose b4e130 b4e20
            | exact resolve b4e20 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e394 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e389
               have i₂ := b4e131 x
               grind)
            | exact superpose b4e131 b4e389
            | exact resolve b4e389 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131 b4e389
          have b4e395 : False := by grind
          exact b4e395
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e36 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b5e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (k (M.op X0 X1) (M.op (M.op X2 X0) X1)) := by
            intro X0 X1 X2
            grind
          have b5e38 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e36 X0 X1 x x X4
               have i₂ := b5e13 X0 X1 x x
               grind)
            | exact superpose b5e13 b5e36
            | exact resolve b5e36 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e49 : x = (M.op y y) ∨ x = (k x y) := by grind
          have b5e63 : x = (k x y) := by
            first
            | (have r₁ := b5e49
               have r₂ := b5e21
               grind)
            | exact resolve b5e49 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e84 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (σ y)
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ y) (σ x)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e116 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e38 x x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e38
            | exact resolve b5e38 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e128 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 x X0
               have i₂ := b5e38 (M.op X0 X1) X2 x
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e158 : x ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e116 y
               grind)
            | exact superpose b5e116 b5e21
            | exact resolve b5e21 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1127 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e84 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e84
          have b5e1128 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1127
               have r₂ := b5e24
               grind)
            | exact resolve b5e1127 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1127
          have b5e1129 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1128
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1128
            | exact resolve b5e1128 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1128
          have b5e1130 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1129
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e1129
            | exact resolve b5e1129 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e1129
          have b5e1131 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1130
               grind)
            | exact superpose b5e1130 b5e20
            | exact resolve b5e20 b5e1130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1133 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = (k (σ x) (M.op (M.op X0 (σ x)) (σ y))) := by
            intro X0
            first
            | (have i₁ := b5e37 (σ x) (σ y) X0
               have i₂ := b5e1130
               grind)
            | exact superpose b5e1130 b5e37
            | exact resolve b5e37 b5e1130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e1139 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b5e1133 x
               have i₂ := b5e128 x (σ x) (σ y)
               grind)
            | exact superpose b5e128 b5e1133
            | exact resolve b5e1133 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128 b5e1133
          have b5e1141 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e1131
               have i₂ := b5e116 x
               grind)
            | exact superpose b5e116 b5e1131
            | exact resolve b5e1131 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e1131
          have b5e1142 : (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b5e1139
               have i₂ := b5e1130
               grind)
            | exact superpose b5e1130 b5e1139
            | exact resolve b5e1139 b5e1130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1130 b5e1139
          have b5e1143 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b5e1142
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e1142
            | exact resolve b5e1142 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1142
          have b5e1212 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1143
               have i₂ := b5e18 x x
               grind)
            | exact superpose b5e18 b5e1143
            | (have j1 := b5e18 x x
               grind)
            | exact resolve b5e1143 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1143
          have b5e1222 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b5e1212
          have b5e1232 : (σ x) = (σ y) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e1222
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e1222
            | exact resolve b5e1222 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1222
          have b5e1233 : x = (M.op x x) := by
            first
            | (have r₁ := b5e1232
               have r₂ := b5e1141
               grind)
            | exact resolve b5e1232 b5e1141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1141 b5e1232
          have b5e1889 : x = y := by
            first
            | (have i₁ := b5e22
               have i₂ := b5e1233
               grind)
            | exact superpose b5e1233 b5e22
            | exact resolve b5e22 b5e1233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1233
          have b5e1903 : False := by grind
          exact b5e1903
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
        have b6e26 : (σ y) = (σ (k x y)) := by
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
        have b6e27 : (k x y) = (τ (σ y)) := by
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
        have b6e28 : y = (k x y) := by
          first
          | (have i₁ := b6e27
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e27
          | exact resolve b6e27 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e41 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X2 (M.op (M.op X3 X0) X1) X4 x
             have i₂ := b6e12 X0 X1 (M.op x X2) X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b6e41 X0 X1 x x X4
             have i₂ := b6e12 X0 X1 x x
             grind)
          | exact superpose b6e12 b6e41
          | exact resolve b6e41 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e45 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e43 (σ y) (σ y) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e43
          | exact resolve b6e43 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          grind
        have b6e63 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0 X1
          grind
        have b6e71 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b6e45
        have b6e76 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e18 x x
             grind)
          | exact superpose b6e18 b6e71
          | exact resolve b6e71 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e93 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e115 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
        have b6e118 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b6e93 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93
        have b6e120 : y = (M.op x y) ∨ y = (M.op x x) := by
          first
          | (have r₁ := b6e115
             have r₂ := b6e20
             grind)
          | exact resolve b6e115 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115
        have b6e141 : y = (M.op x y) := by
          first
          | (have r₁ := b6e120
             have r₂ := b6e21
             grind)
          | exact resolve b6e120 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e153 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e43 x y x
             have i₂ := b6e141
             grind)
          | exact superpose b6e141 b6e43
          | exact resolve b6e43 b6e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e171 : x ≠ y := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e153 y
             grind)
          | exact superpose b6e153 b6e20
          | exact resolve b6e20 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e379 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e13
          | exact resolve b6e13 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e381 : x = (k x x) := by
          first
          | (have i₁ := b6e379
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e379
          | exact resolve b6e379 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e379
        have b6e455 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e381
             grind)
          | exact superpose b6e381 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e381
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e381
        have b6e456 : x = (M.op x x) := by grind
        clear b6e455
        have b6e471 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e62 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e475 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
          intro X0
          first
          | (have j0 := b6e471 X0
             have j1 := b6e63 X0 x
             grind)
          | (have r₁ := b6e471 X0
             have r₂ := b6e63 X0 X0
             grind)
          | exact resolve b6e471 b6e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63 b6e471
        have b6e493 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e43 x x x
             have i₂ := b6e456
             grind)
          | exact superpose b6e456 b6e43
          | exact resolve b6e43 b6e456
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43 b6e456
        have b6e722 : (σ y) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e475 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e475
          | exact resolve b6e475 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e475
        have b6e727 : (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e722
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e722
          | exact resolve b6e722 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e722
        have b6e828 : (τ (σ y)) = (k y x) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e727
             grind)
          | exact superpose b6e727 b6e13
          | exact resolve b6e13 b6e727
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e727
        have b6e829 : y = (k y x) := by
          first
          | (have i₁ := b6e828
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e828
          | exact resolve b6e828 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e828
        have b6e899 : x = y ∨ x = (M.op y y) ∨ (k y x) = (M.op y x) := by
          first
          | (have i₁ := b6e28
             have i₂ := b6e118 y x
             grind)
          | exact superpose b6e118 b6e28
          | (have j1 := b6e118 y x
             grind)
          | exact resolve b6e28 b6e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28 b6e118
        have b6e923 : x = (M.op y y) ∨ (k y x) = (M.op y x) := by
          first
          | (have r₁ := b6e899
             have r₂ := b6e171
             grind)
          | exact resolve b6e899 b6e171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e899
        have b6e948 : (k y x) = (M.op y x) := by
          first
          | (have r₁ := b6e923
             have r₂ := b6e20
             grind)
          | exact resolve b6e923 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e923
        have b6e962 : x = (k y x) := by
          first
          | (have i₁ := b6e948
             have i₂ := b6e493 y
             grind)
          | exact superpose b6e493 b6e948
          | exact resolve b6e948 b6e493
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e493 b6e948
        have b6e973 : x = y := by
          first
          | (have i₁ := b6e962
             have i₂ := b6e829
             grind)
          | exact superpose b6e829 b6e962
          | exact resolve b6e962 b6e829
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e829 b6e962
        have b6e978 : False := by grind
        exact b6e978
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
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
          have b7e27 : (σ x) = (k (σ y) (σ x)) := by grind
          have b7e28 : (σ x) = (σ (k y x)) := by
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
          have b7e33 : (k y x) = (τ (σ x)) := by
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
          have b7e34 : x = (k y x) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e33
            | exact resolve b7e33 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e39 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b7e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e39 X0 X1 x x X4
               have i₂ := b7e13 X0 X1 x x
               grind)
            | exact superpose b7e13 b7e39
            | exact resolve b7e39 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e52 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          have b7e57 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            grind
          have b7e64 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 (M.op X0 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e57 X0 X1
               have i₂ := b7e41 X0 X0 X0
               grind)
            | exact superpose b7e41 b7e57
            | (have j0 := b7e57 X0 X1
               grind)
            | exact resolve b7e57 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e66 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e52
               have r₂ := b7e23
               grind)
            | exact resolve b7e52 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e67 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e70 : (τ (σ x)) = (k x y) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e14
            | exact resolve b7e14 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e71 : x = (k x y) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e70
            | exact resolve b7e70 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e110 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
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
          have b7e115 : x = (M.op y x) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b7e110
               have r₂ := b7e22
               grind)
            | exact resolve b7e110 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e136 : x = (M.op y x) := by
            first
            | (have r₁ := b7e115
               have r₂ := b7e21
               grind)
            | exact resolve b7e115 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e150 : x = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
          have b7e151 : x = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e150
               have r₂ := b7e21
               grind)
            | exact resolve b7e150 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e150
          have b7e153 : x = (M.op x y) := by
            first
            | (have r₁ := b7e151
               have r₂ := b7e22
               grind)
            | exact resolve b7e151 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e151
          have b7e160 : ∀ X0 : G, x = (M.op X0 x) := by
            intro X0
            first
            | (have i₁ := b7e41 y x x
               have i₂ := b7e136
               grind)
            | exact superpose b7e136 b7e41
            | exact resolve b7e41 b7e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e174 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 y X0 X1 x
               have i₂ := b7e153
               grind)
            | exact superpose b7e153 b7e13
            | exact resolve b7e13 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e175 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b7e174 X0 x
               have i₂ := b7e41 x X0 x
               grind)
            | exact superpose b7e41 b7e174
            | exact resolve b7e174 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e174
          have b7e222 : x ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e160 x
               grind)
            | exact superpose b7e160 b7e22
            | exact resolve b7e22 b7e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e160
          have b7e328 : ∀ X0 : G, x ≠ (M.op X0 y) ∨ y = (k y (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e21
               have i₂ := b7e64 y X0
               grind)
            | (have i₁ := b7e21
               have i₂ := b7e64 y y
               grind)
            | exact superpose b7e64 b7e21
            | (have j1 := b7e64 y x
               grind)
            | exact resolve b7e21 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e342 : ∀ X0 : G, y = (k y (M.op x y)) ∨ x ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e328 X0
               have i₂ := b7e175 y
               grind)
            | exact superpose b7e175 b7e328
            | (have j0 := b7e328 X0
               grind)
            | exact resolve b7e328 b7e175
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e175 b7e328
          have b7e357 : ∀ X0 : G, y = (k y x) ∨ x ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e342 X0
               have i₂ := b7e153
               grind)
            | exact superpose b7e153 b7e342
            | (have j0 := b7e342 X0
               grind)
            | (have r₁ := b7e342 x
               have r₂ := b7e153
               grind)
            | exact resolve b7e342 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e342
          have b7e363 : ∀ X0 : G, x = y ∨ x ≠ (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e357 X0
               have i₂ := b7e34
               grind)
            | exact superpose b7e34 b7e357
            | (have j0 := b7e357 X0
               grind)
            | exact resolve b7e357 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e357
          have b7e365 : ∀ X0 : G, x ≠ (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b7e363 X0
               grind)
            | (have r₁ := b7e363 X0
               have r₂ := b7e222
               grind)
            | exact resolve b7e363 b7e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e222 b7e363
          have b7e370 : x ≠ x := by
            first
            | (have i₁ := b7e365 x
               have i₂ := b7e153
               grind)
            | exact superpose b7e153 b7e365
            | (have r₁ := b7e365 x
               have r₂ := b7e153
               grind)
            | exact resolve b7e365 b7e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153 b7e365
          have b7e371 : False := by grind
          exact b7e371
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
          have b8e97 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e916 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e97 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e917 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e916
               have r₂ := b8e24
               grind)
            | exact resolve b8e916 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e916
          have b8e918 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e917
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e917
            | exact resolve b8e917 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e917
          have b8e919 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e918
               grind)
            | exact superpose b8e918 b8e20
            | exact resolve b8e20 b8e918
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e918
          have b8e936 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e919
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e919
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e919 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e919
          have b8e941 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e936
          have b8e944 : y = (M.op x x) := by
            first
            | (have r₁ := b8e941
               have r₂ := b8e21
               grind)
            | exact resolve b8e941 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e941
          have b8e946 : False := by grind
          exact b8e946

/-- `Equation3634`: `x ◇ y = z ◇ ((w ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_x_y_pxy_Equation3634 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3634 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3634.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
        intro X0 X1 X2 X3
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e29 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 y X0 X1 y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X2 (M.op (M.op X3 X0) X1) X4 x
           have i₂ := b0e11 X0 X1 (M.op x X2) X3
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
        intro X0 X1 X4
        first
        | (have i₁ := b0e32 X0 X1 x x X4
           have i₂ := b0e11 X0 X1 x x
           grind)
        | exact superpose b0e11 b0e32
        | exact resolve b0e32 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e36 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e29 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e29
        | exact resolve b0e29 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e83 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e34 (σ y) (σ y) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e34
        | exact resolve b0e34 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e104 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e83 (σ x)
           grind)
        | exact superpose b0e83 b0e18
        | exact resolve b0e18 b0e83
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e83
      have b0e108 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e104
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e104
        | exact resolve b0e104 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e104
      have b0e109 : False := by grind
      exact b0e109
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b1e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e47 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e21
             grind)
          | exact resolve b1e46 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e47
          | exact resolve b1e47 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e49 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e25 x
             grind)
          | exact superpose b1e25 b1e48
          | exact resolve b1e48 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e48
        have b1e50 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e22
          | exact resolve b1e22 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e57 : False := by grind
        exact b1e57
      · have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e24 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b2e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23
        have b2e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 (τ X0) X1
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e18
          | exact resolve b2e18 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e104 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b2e25 X0 y
             have i₂ := b2e24 (τ X0)
             grind)
          | exact superpose b2e24 b2e25
          | exact resolve b2e25 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e25
        have b2e113 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e104 X0
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e104
          | exact resolve b2e104 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104
        have b2e116 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b2e17 X0 (σ y)
             have i₂ := b2e113 X0
             grind)
          | exact superpose b2e113 b2e17
          | (have j0 := b2e17 X0 (σ y)
             grind)
          | exact resolve b2e17 b2e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e119 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b2e116 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116
        have b2e122 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b2e119 X0
             grind)
          | (have r₁ := b2e119 (σ y)
             have r₂ := b2e21
             grind)
          | (have r₁ := b2e119 X0
             have r₂ := b2e21
             grind)
          | exact resolve b2e119 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e119
        have b2e141 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e122 (σ x)
             grind)
          | exact superpose b2e122 b2e22
          | (have r₁ := b2e22
             have r₂ := b2e122 (σ x)
             grind)
          | exact resolve b2e22 b2e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e122
        have b2e144 : False := by grind
        exact b2e144
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b3e24 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e29 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 y
             have i₂ := b3e25 (σ X0)
             grind)
          | exact superpose b3e25 b3e18
          | exact resolve b3e18 b3e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25
        have b3e39 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b3e13 (k X0 y)
             have i₂ := b3e29 X0
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e40 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e39 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e39
          | exact resolve b3e39 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39
        have b3e43 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
        have b3e45 : y = (M.op y y) ∨ y = (k x y) := by grind
        clear b3e43
        have b3e46 : y = (k x y) := by
          first
          | (have r₁ := b3e45
             have r₂ := b3e20
             grind)
          | exact resolve b3e45 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e47 : x = y := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e40 x
             grind)
          | exact superpose b3e40 b3e46
          | exact resolve b3e46 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40 b3e46
        have b3e49 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e21
          | exact resolve b3e21 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e50 : False := by grind
        exact b3e50
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e26 : (σ x) ≠ (σ x) := by
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
        · have b5e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e34 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b5e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e34 X0 X1 x x X4
               have i₂ := b5e13 X0 X1 x x
               grind)
            | exact superpose b5e13 b5e34
            | exact resolve b5e34 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e48 : x ≠ x ∨ y = (M.op y y) ∨ y = (k x y) := by
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
          have b5e51 : y = (M.op y y) ∨ y = (k x y) := by grind
          clear b5e48
          have b5e52 : y = (k x y) := by
            first
            | (have r₁ := b5e51
               have r₂ := b5e21
               grind)
            | exact resolve b5e51 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e327 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op X2 (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 (σ X0) (σ X1) x
               have i₂ := b5e57 X0 X1
               grind)
            | exact superpose b5e57 b5e36
            | (have j1 := b5e57 X1 X1
               grind)
            | exact resolve b5e36 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e57
          have b5e3081 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e327 x y x
               have i₂ := b5e52
               grind)
            | exact superpose b5e52 b5e327
            | (have j0 := b5e327 y y x
               grind)
            | exact resolve b5e327 b5e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52 b5e327
          have b5e3161 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have j0 := b5e3081 X0
               grind)
            | (have r₁ := b5e3081 (σ y)
               have r₂ := b5e23
               grind)
            | (have r₁ := b5e3081 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e3081 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3081
          have b5e3176 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e3161 X0
               grind)
            | (have r₁ := b5e3161 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e3161 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3161
          have b5e3190 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e3176 (σ y)
               grind)
            | exact superpose b5e3176 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e3176 (σ y)
               grind)
            | exact resolve b5e23 b5e3176
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3176
          have b5e3226 : False := by grind
          exact b5e3226
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b6e23 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e28 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
          intro X0
          first
          | (have i₁ := b6e24 (σ X0)
             have i₂ := b6e18 X0 y
             grind)
          | exact superpose b6e18 b6e24
          | exact resolve b6e24 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e31 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b6e13 (k X0 y)
             have i₂ := b6e28 X0
             grind)
          | exact superpose b6e28 b6e13
          | exact resolve b6e13 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e32 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e31 X0
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e67 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b6e32 X0
             have i₂ := b6e17 X0 y
             grind)
          | exact superpose b6e17 b6e32
          | (have j1 := b6e17 X0 y
             grind)
          | exact resolve b6e32 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e75 : ∀ X0 : G, (M.op X0 y) = X0 ∨ y = (M.op y y) := by
          intro X0
          first
          | (have j0 := b6e67 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e67
        have b6e81 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b6e75 X0
             grind)
          | (have r₁ := b6e75 y
             have r₂ := b6e20
             grind)
          | (have r₁ := b6e75 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e75 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e75
        have b6e84 : x ≠ x := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e81 x
             grind)
          | exact superpose b6e81 b6e21
          | (have r₁ := b6e21
             have r₂ := b6e81 x
             grind)
          | exact resolve b6e21 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e92 : False := by grind
        exact b6e92
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op (M.op X3 X0) X1)) := by
            intro X0 X1 X2 X3
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 (M.op (M.op X3 X0) X1)) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 X2 (M.op (M.op X3 X0) X1) X4 x
               have i₂ := b7e13 X0 X1 (M.op x X2) X3
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 X1 X4 : G, (M.op X0 X1) = (M.op X4 (M.op X0 X1)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b7e30 X0 X1 x x X4
               have i₂ := b7e13 X0 X1 x x
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e44
          have b7e48 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e47
               have r₂ := b7e23
               grind)
            | exact resolve b7e47 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e49 : (σ y) = (σ (k x y)) := by
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
          have b7e72 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e73 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e21
               grind)
            | exact resolve b7e72 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e75 : y = (M.op x y) := by
            first
            | (have r₁ := b7e73
               have r₂ := b7e22
               grind)
            | exact resolve b7e73 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e85 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e32 x y x
               have i₂ := b7e75
               grind)
            | exact superpose b7e75 b7e32
            | exact resolve b7e32 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e75
          have b7e147 : y ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e85 y
               grind)
            | exact superpose b7e85 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e85 y
               grind)
            | exact resolve b7e21 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e159 : False := by grind
          exact b7e159
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e219 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e48 x y
               grind)
            | exact superpose b8e48 b8e20
            | (have j1 := b8e48 y y
               grind)
            | exact resolve b8e20 b8e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e257 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e219
               have r₂ := b8e23
               grind)
            | exact resolve b8e219 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e261 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e257
               have r₂ := b8e24
               grind)
            | exact resolve b8e257 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e257
          have b8e262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e261
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e261
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e261 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e261
          have b8e263 : y = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e262
          have b8e264 : x = (M.op x y) := by
            first
            | (have r₁ := b8e263
               have r₂ := b8e21
               grind)
            | exact resolve b8e263 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e263
          have b8e265 : False := by grind
          exact b8e265

/-- `Equation3673`: `x ◇ x = (x ◇ y) ◇ (z ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_y_pxy_Equation3673 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3673 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3673.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
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
          have b5e58 : y ≠ y ∨ x = y ∨ y = (k x y) := by
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
          have b5e60 : x = y ∨ y = (k x y) := by grind
          clear b5e58
          have b5e62 : y = (k x y) := by
            first
            | (have r₁ := b5e60
               have r₂ := b5e21
               grind)
            | exact resolve b5e60 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e451 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have j0 := b5e65 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e18327 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e451 x y
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e451
            | (have j0 := b5e451 x y
               grind)
            | exact resolve b5e451 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62 b5e451
          have b5e18330 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          clear b5e18327
          have b5e18334 : (σ x) = (σ y) := by
            first
            | (have r₁ := b5e18330
               have r₂ := b5e24
               grind)
            | exact resolve b5e18330 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e18330
          have b5e18338 : False := by grind
          exact b5e18338
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
          have b7e51 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e53 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e51
          have b7e54 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e53
               have r₂ := b7e23
               grind)
            | exact resolve b7e53 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e55 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e54
            | exact resolve b7e54 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e65 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e55
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e55 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e66 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e26
               grind)
            | exact resolve b7e65 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e65
          have b7e67 : x = y := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e22
               grind)
            | exact resolve b7e66 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e68 : False := by grind
          exact b7e68
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
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e273 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e61 x y
               grind)
            | exact superpose b8e61 b8e20
            | (have j1 := b8e61 x y
               grind)
            | exact resolve b8e20 b8e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e291 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e273
               have r₂ := b8e24
               grind)
            | exact resolve b8e273 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273
          have b8e296 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e291
               have r₂ := b8e23
               grind)
            | exact resolve b8e291 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e291
          have b8e299 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e296
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e296
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e296
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e296
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e296 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e296
          have b8e300 : y = (M.op x y) ∨ x = y := by grind
          clear b8e299
          have b8e301 : x = y := by
            first
            | (have r₁ := b8e300
               have r₂ := b8e22
               grind)
            | exact resolve b8e300 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e300
          have b8e302 : False := by grind
          exact b8e302

/-- `Equation3714`: `x ◇ y = (x ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation3714 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3714 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3714.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = y := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e28
      have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e79 : False := by grind
      exact b0e79
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e28 : False := by grind
        exact b1e28
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e28 : False := by grind
        exact b2e28
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) (M.op X1 X0)) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e33 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e13 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op y y) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b4e57 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X1
               have i₂ := b4e18 (M.op X1 X1) X0
               grind)
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e18 X0 (M.op (M.op X0 X0) (M.op X1 X0))
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 (M.op X1 X1) X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e59 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e60 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e57 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e52 X0 X1
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e52
            | (have j0 := b4e52 X0 X1
               grind)
            | exact resolve b4e52 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52
          have b4e213 : ∀ X0 : G, y ≠ y ∨ (M.op y X0) = (k y X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e59 X0 y
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e59
            | (have j0 := b4e59 X0 y
               grind)
            | (have r₁ := b4e59 X0 y
               have r₂ := b4e36
               grind)
            | exact resolve b4e59 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e214 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b4e213 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e213
          have b4e220 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = y := by
            intro X0
            first
            | (have i₁ := b4e28 X0 y
               have i₂ := b4e214 (τ X0)
               grind)
            | exact superpose b4e214 b4e28
            | (have j1 := b4e214 (τ X0)
               grind)
            | exact resolve b4e28 b4e214
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e28 b4e214
          have b4e262 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e60 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e60
            | exact resolve b4e60 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e451 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (M.op (σ y) (σ (k X0 x))) ∨ (σ x) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e34 (σ X0)
               have i₂ := b4e63 X0 x
               grind)
            | exact superpose b4e63 b4e34
            | (have j1 := b4e63 X0 x
               grind)
            | exact resolve b4e34 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e63
          have b4e536 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e19 y X0
               have i₂ := b4e262 (σ X0)
               grind)
            | exact superpose b4e262 b4e19
            | (have j1 := b4e262 (σ X0)
               grind)
            | exact resolve b4e19 b4e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e262
          have b4e854 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e220 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e220
            | exact resolve b4e220 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e220
          have b4e884 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b4e854 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e854
            | (have j0 := b4e854 X0
               grind)
            | exact resolve b4e854 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e854
          have b4e7437 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b4e451 y
               have i₂ := b4e884 x
               grind)
            | exact superpose b4e884 b4e451
            | (have j0 := b4e451 y
               have j1 := b4e884 x
               grind)
            | exact resolve b4e451 b4e884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e451
          have b4e7559 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ (σ x) = (σ (M.op y y)) ∨ x = y := by
            first
            | (have r₁ := b4e7437
               have r₂ := b4e23
               grind)
            | exact resolve b4e7437 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7437
          have b4e7562 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e7559
               have r₂ := b4e21
               grind)
            | exact resolve b4e7559 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7559
          have b4e7564 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have i₁ := b4e7562
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e7562
            | exact resolve b4e7562 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7562
          have b4e7566 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ (M.op y x))) := by
            first
            | (have r₁ := b4e7564
               have r₂ := b4e23
               grind)
            | exact resolve b4e7564 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7564
          have b4e7574 : (M.op (σ x) (σ y)) = (σ (k y (M.op y x))) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e536 (M.op y x)
               have i₂ := b4e7566
               grind)
            | exact superpose b4e7566 b4e536
            | (have j0 := b4e536 (M.op y x)
               grind)
            | exact resolve b4e536 b4e7566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e536
          have b4e59767 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y x))) ∨ y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e884 (M.op y x)
               have i₂ := b4e7574
               grind)
            | exact superpose b4e7574 b4e884
            | (have j0 := b4e884 (M.op y x)
               grind)
            | exact resolve b4e884 b4e7574
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e884 b4e7574
          have b4e59773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e59767
               have i₂ := b4e33 y
               grind)
            | exact superpose b4e33 b4e59767
            | exact resolve b4e59767 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59767
          have b4e59777 : (σ y) = (σ (M.op y x)) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b4e59773
               have r₂ := b4e20
               grind)
            | exact resolve b4e59773 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59773
          have b4e59793 : (M.op y x) = (τ (σ y)) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e14 (M.op y x)
               have i₂ := b4e59777
               grind)
            | exact superpose b4e59777 b4e14
            | exact resolve b4e14 b4e59777
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59777
          have b4e59911 : y = (M.op y x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b4e59793
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e59793
            | exact resolve b4e59793 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59793
          have b4e59912 : y = (M.op y x) := by grind
          clear b4e59911
          have b4e59924 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e7566
               have i₂ := b4e59912
               grind)
            | exact superpose b4e59912 b4e7566
            | exact resolve b4e7566 b4e59912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e7566
          have b4e59930 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b4e33 y
               have i₂ := b4e59912
               grind)
            | exact superpose b4e59912 b4e33
            | exact resolve b4e33 b4e59912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e59912
          have b4e59991 : y = (M.op x y) := by
            first
            | (have i₁ := b4e59930
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e59930
            | exact resolve b4e59930 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59930
          have b4e59995 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e59924
               have i₂ := b4e31 y
               grind)
            | exact superpose b4e31 b4e59924
            | exact resolve b4e59924 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e59924
          have b4e60012 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e59995
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e59995
            | exact resolve b4e59995 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e59995
          have b4e60134 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e60012
               grind)
            | exact superpose b4e60012 b4e20
            | exact resolve b4e20 b4e60012
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60012
          have b4e60241 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e60134
               have i₂ := b4e59991
               grind)
            | exact superpose b4e59991 b4e60134
            | exact resolve b4e60134 b4e59991
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59991 b4e60134
          have b4e60242 : False := by grind
          exact b4e60242
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e89 : (σ y) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 x
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e96 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e89
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e89
            | exact resolve b5e89 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e89
          have b5e97 : False := by grind
          exact b5e97
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e13
          | exact resolve b6e13 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : x = y := by
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
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e111 : (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 x
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e153 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e111
               grind)
            | exact superpose b7e111 b7e14
            | exact resolve b7e14 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111
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
          have b7e158 : False := by grind
          exact b7e158
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = X0 := by
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
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ x) (σ x))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ x) (σ x)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e216 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e65 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e217 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e216
               have r₂ := b8e23
               grind)
            | exact resolve b8e216 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216
          have b8e218 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e217
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e217
            | exact resolve b8e217 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e217
          have b8e219 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e218
               grind)
            | exact superpose b8e218 b8e20
            | exact resolve b8e20 b8e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e218
          have b8e254 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e219
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e219
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e219
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e219
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e219 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e255 : y = (M.op x x) ∨ x = y := by grind
          clear b8e254
          have b8e258 : x = y := by
            first
            | (have r₁ := b8e255
               have r₂ := b8e22
               grind)
            | exact resolve b8e255 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e255
          have b8e261 : False := by grind
          exact b8e261

/-- `Equation3756`: `x ◇ y = (y ◇ x) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pxy_pyx_Equation3756 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3756 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3756.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e68 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e73 : False := by grind
      exact b0e73
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : False := by grind
        exact b1e26
      · have b2e20 : x = y := by grind
        have b2e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e26 : False := by grind
        exact b2e26
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e32 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
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
          have b4e35 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X0 X0) y X1
               have i₂ := b4e32 X0
               grind)
            | exact superpose b4e32 b4e13
            | exact resolve b4e13 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b4e42 X0 x
               have i₂ := b4e32 x
               grind)
            | exact superpose b4e32 b4e42
            | exact resolve b4e42 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e42
          have b4e44 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b4e43 X0
               have i₂ := b4e35 X0 X0
               grind)
            | exact superpose b4e35 b4e43
            | exact resolve b4e43 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e43
          have b4e60 : y = (σ y) := by
            first
            | (have i₁ := b4e24
               have i₂ := b4e44 (σ y)
               grind)
            | exact superpose b4e44 b4e24
            | exact resolve b4e24 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e18 (σ X1) (σ X0)
               grind)
            | exact superpose b4e18 b4e19
            | (have j1 := b4e18 (M.op (σ X0) (σ X0)) (σ X0)
               grind)
            | exact resolve b4e19 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e63 X0 X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e63
            | (have j0 := b4e63 X0 X1
               grind)
            | exact resolve b4e63 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e63
          have b4e73 : ∀ X0 X1 : G, (σ X0) = (σ y) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e71 X0 X1
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e71
            | (have j0 := b4e71 X0 X1
               grind)
            | exact resolve b4e71 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e75 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = y ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e73 X0 X1
               have i₂ := b4e60
               grind)
            | exact superpose b4e60 b4e73
            | (have j0 := b4e73 X0 X1
               grind)
            | exact resolve b4e73 b4e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e545 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (σ x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e75 x y
               grind)
            | exact superpose b4e75 b4e20
            | (have j1 := b4e75 x y
               grind)
            | exact resolve b4e20 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75
          have b4e556 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (σ x) := by
            first
            | (have r₁ := b4e545
               have r₂ := b4e23
               grind)
            | exact resolve b4e545 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e545
          have b4e721 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (σ x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e556
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e556
            | (have j1 := b4e18 (M.op x x) x
               grind)
            | (have r₁ := b4e556
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e556
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e556 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e556
          have b4e722 : y = (σ x) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b4e721
          have b4e725 : y = (σ x) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b4e722
               have r₂ := b4e21
               grind)
            | exact resolve b4e722 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e722
          have b4e728 : x = y ∨ y = (σ x) := by
            first
            | (have i₁ := b4e725
               have i₂ := b4e44 x
               grind)
            | exact superpose b4e44 b4e725
            | exact resolve b4e725 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e725
          have b4e729 : y = (σ x) := by
            first
            | (have r₁ := b4e728
               have r₂ := b4e21
               grind)
            | exact resolve b4e728 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e728
          have b4e731 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e729
               grind)
            | exact superpose b4e729 b4e23
            | exact resolve b4e23 b4e729
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e729
          have b4e750 : False := by grind
          exact b4e750
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
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
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e32 : ∀ X0 : G, y = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 y y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e39 : ∀ X0 X1 : G, (M.op (M.op X0 X0) y) = (M.op y (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X0 X0) y X1
               have i₂ := b5e32 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e40 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
            intro X0
            first
            | (have i₁ := b5e39 X0 x
               have i₂ := b5e32 x
               grind)
            | exact superpose b5e32 b5e39
            | exact resolve b5e39 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e39
          have b5e41 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b5e40 X0
               have i₂ := b5e34 X0 X0
               grind)
            | exact superpose b5e34 b5e40
            | exact resolve b5e40 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e40
          have b5e54 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e41 (σ y)
               grind)
            | exact superpose b5e41 b5e24
            | exact resolve b5e24 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e95 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e26
          have b5e101 : ∀ X0 : G, (σ y) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e95 X0
               have i₂ := b5e41 (τ X0)
               grind)
            | exact superpose b5e41 b5e95
            | exact resolve b5e95 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e102 : ∀ X0 : G, (σ y) = (k X0 X0) := by
            intro X0
            first
            | (have i₁ := b5e101 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e101
            | exact resolve b5e101 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e101
          have b5e105 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
            intro X0
            grind
          clear b5e102
          have b5e110 : y = (σ y) := by
            first
            | (have i₁ := b5e105 x
               have i₂ := b5e41 x
               grind)
            | exact superpose b5e41 b5e105
            | exact resolve b5e105 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e105
          have b5e114 : False := by grind
          exact b5e114
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b7e32 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ y) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e34 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ y) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op X0 X0) (σ y) X1
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e13
            | exact resolve b7e13 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e39 X0 x
               have i₂ := b7e32 x
               grind)
            | exact superpose b7e32 b7e39
            | exact resolve b7e39 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e39
          have b7e41 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e40 X0
               have i₂ := b7e34 X0 X0
               grind)
            | exact superpose b7e34 b7e40
            | exact resolve b7e40 b7e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34 b7e40
          have b7e54 : y ≠ (σ y) := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e41 y
               grind)
            | exact superpose b7e41 b7e22
            | exact resolve b7e22 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b7e26
          have b7e76 : ∀ X0 : G, (σ (σ y)) = (k X0 (σ (τ X0))) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e41 (τ X0)
               grind)
            | exact superpose b7e41 b7e70
            | exact resolve b7e70 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e77 : ∀ X0 : G, (k X0 X0) = (σ (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e76 X0
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e76
            | exact resolve b7e76 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e80 : ∀ X0 : G, (M.op X0 X0) = (σ (σ y)) := by
            intro X0
            grind
          clear b7e77
          have b7e85 : (σ y) = (σ (σ y)) := by
            first
            | (have i₁ := b7e80 x
               have i₂ := b7e41 x
               grind)
            | exact superpose b7e41 b7e80
            | exact resolve b7e80 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e80
          have b7e110 : (σ y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (σ y)
               have i₂ := b7e85
               grind)
            | exact superpose b7e85 b7e14
            | exact resolve b7e14 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e111 : y = (σ y) := by
            first
            | (have i₁ := b7e110
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e110
            | exact resolve b7e110 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e114 : False := by grind
          exact b7e114
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X0) (M.op X2 X2)) := by
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
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X0)) = (M.op (M.op X0 X1) (M.op X3 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 (M.op X2 X2) (M.op X1 X0) X3
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e34 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X2) (M.op X1 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e32 X0 X1 X2 x
               have i₂ := b8e13 X1 X0 x
               grind)
            | exact superpose b8e13 b8e32
            | exact resolve b8e32 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e36 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b8e39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e40 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e36 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e36
            | exact resolve b8e36 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e41 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b8e40
          have b8e42 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 (M.op X0 X0)
               have i₂ := b8e13 X0 X0 X0
               grind)
            | exact superpose b8e13 b8e17
            | (have j0 := b8e17 (M.op X0 X0) X1
               grind)
            | (have r₁ := b8e17 X0 (M.op x x)
               have r₂ := b8e13 x x x
               grind)
            | exact resolve b8e17 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e43 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e42 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42
          have b8e50 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b8e57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e18 (σ X1) (σ X0)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X0) (σ X0)) (σ X0)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e59 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = X0 ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X1 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X2 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e18 X2 X0
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X2 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 (M.op X1 X1) X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 (M.op X0 X0)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (σ y)
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 X0 (σ y)
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ y) (M.op (σ y) (σ y))
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (M.op (σ y) (σ y)) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e63 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b8e62 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e64 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X2) = (k X2 X0) ∨ X0 = X1 ∨ X0 = X2 := by
            intro X0 X1 X2
            first
            | (have j0 := b8e60 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e57 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e57
            | (have j0 := b8e57 X0 X1
               grind)
            | exact resolve b8e57 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e57
          have b8e75 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X2 X1) (σ (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X2 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e13
            | exact resolve b8e13 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (M.op X1 X1) (σ (M.op X0 X0))) := by
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
          have b8e85 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X0 X1
               have i₂ := b8e34 X1 X1 X0
               grind)
            | exact superpose b8e34 b8e13
            | exact resolve b8e13 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e91 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e83 X0 X1
               have i₂ := b8e75 X0 X1 X1
               grind)
            | exact superpose b8e75 b8e83
            | exact resolve b8e83 b8e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e75 b8e83
          have b8e93 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 y
               have i₂ := b8e63 (σ X0)
               grind)
            | exact superpose b8e63 b8e19
            | (have j1 := b8e63 (σ X0)
               grind)
            | exact resolve b8e19 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e127 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e85 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e85 X0 (σ y)
               grind)
            | exact superpose b8e85 b8e24
            | exact resolve b8e24 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e130 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e85 y X0
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e85 X0 y
               grind)
            | exact superpose b8e85 b8e22
            | exact resolve b8e22 b8e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e252 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e64 X1 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e255 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e252 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e252
          have b8e288 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e65 x y
               grind)
            | exact superpose b8e65 b8e20
            | (have j1 := b8e65 x (M.op x x)
               grind)
            | exact resolve b8e20 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e291 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (M.op (σ (k X0 X1)) (M.op X2 X2)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 (σ X0) (σ X1) X2
               have i₂ := b8e65 X1 X0
               grind)
            | exact superpose b8e65 b8e13
            | (have j1 := b8e65 X1 (M.op X1 X1)
               grind)
            | exact resolve b8e13 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e301 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e288
               have r₂ := b8e23
               grind)
            | exact resolve b8e288 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e288
          have b8e333 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e91 (σ X0) X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e91
            | exact resolve b8e91 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e358 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1
               have i₂ := b8e91 X0 (σ X1)
               grind)
            | exact superpose b8e91 b8e30
            | exact resolve b8e30 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e368 : ∀ X0 X1 X2 : G, (σ (k (M.op X1 X1) X2)) = (k (M.op X0 X0) (σ X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e19 (M.op X1 X1) X2
               have i₂ := b8e91 X1 X0
               grind)
            | exact superpose b8e91 b8e19
            | exact resolve b8e19 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e369 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (M.op X1 X1)
               have i₂ := b8e91 X1 X0
               grind)
            | exact superpose b8e91 b8e14
            | exact resolve b8e14 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e384 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e369 x X1
               have i₂ := b8e369 X0 x
               grind)
            | exact superpose b8e369 b8e369
            | exact resolve b8e369 b8e369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e429 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e39 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e39
            | exact resolve b8e39 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e432 : ∀ X0 X1 X2 : G, (k (τ X1) (M.op X2 X2)) = (τ (k X1 (M.op X0 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e39 X1 (M.op X2 X2)
               have i₂ := b8e91 X2 X0
               grind)
            | exact superpose b8e91 b8e39
            | exact resolve b8e39 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e503 : ∀ X0 X1 X2 : G, (k (M.op X1 X1) (τ X2)) = (τ (k (M.op X0 X0) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e50 (M.op X1 X1) X2
               have i₂ := b8e91 X1 X0
               grind)
            | exact superpose b8e91 b8e50
            | exact resolve b8e50 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e50
          have b8e1183 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) y)) = (M.op (σ y) (M.op X0 X0)) ∨ (M.op X0 X0) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b8e93 (M.op X0 X0)
               have i₂ := b8e91 X0 X1
               grind)
            | exact superpose b8e91 b8e93
            | exact resolve b8e93 b8e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e91
          have b8e1199 : ∀ X0 X1 : G, (σ (k (M.op X1 X1) y)) = (M.op (σ y) (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e1183 X0 X1
               grind)
            | (have r₁ := b8e1183 X0 X1
               have r₂ := b8e127 X0
               grind)
            | exact resolve b8e1183 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1183
          have b8e1258 : ∀ X0 X2 : G, (τ (τ (M.op X0 X0))) = (σ (σ (M.op X2 X2))) := by
            intro X0 X2
            first
            | (have i₁ := b8e333 X2 x
               have i₂ := b8e384 X0 x
               grind)
            | exact superpose b8e384 b8e333
            | exact resolve b8e333 b8e384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e333
          have b8e1274 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (τ (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1
               have i₂ := b8e384 X0 (σ X1)
               grind)
            | exact superpose b8e384 b8e30
            | exact resolve b8e30 b8e384
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e384
          have b8e1310 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e301
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e301
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e301
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e301
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e301 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e301
          have b8e1311 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e1310
          have b8e1313 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e1311
               have r₂ := b8e21
               grind)
            | exact resolve b8e1311 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1311
          have b8e1654 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) (M.op X2 X2)) = (k (M.op X2 X2) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e255 (M.op X2 X2) (M.op X0 X1)
               have i₂ := b8e34 X1 X0 X2
               grind)
            | exact superpose b8e34 b8e255
            | (have j0 := b8e255 (M.op X2 X2) (M.op X0 X1)
               grind)
            | exact resolve b8e255 b8e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34 b8e255
          have b8e1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (k (M.op X2 X2) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e1654 X0 X1 X2
               have j1 := b8e59 (M.op X0 X1) X1 (M.op X2 X2)
               grind)
            | (have r₁ := b8e1654 X0 X1 X1
               have r₂ := b8e59 (M.op X0 X1) X1 X2
               grind)
            | (have r₁ := b8e1654 X0 X1 X2
               have r₂ := b8e59 (M.op X0 X1) X1 (M.op (M.op X0 X1) (M.op X2 X2))
               grind)
            | (have r₁ := b8e1654 X0 X1 X2
               have r₂ := b8e59 (M.op (M.op X0 X1) (M.op X2 X2)) X1 (M.op X0 X1)
               grind)
            | exact resolve b8e1654 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59 b8e1654
          have b8e1689 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (M.op X2 X2) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1685 X0 X1 X2
               have i₂ := b8e13 X1 X0 X2
               grind)
            | exact superpose b8e13 b8e1685
            | (have j0 := b8e1685 X0 X1 X2
               grind)
            | exact resolve b8e1685 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1685
          have b8e8943 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e1313
               grind)
            | exact superpose b8e1313 b8e14
            | exact resolve b8e14 b8e1313
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1313
          have b8e8984 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e8943
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e8943
            | exact resolve b8e8943 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8943
          have b8e8985 : x = (M.op x x) := by grind
          clear b8e8984
          have b8e9190 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 X0) x) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 X1 x
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e13
            | exact resolve b8e13 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e9202 : ∀ X0 : G, (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b8e85 X0 x
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e85
            | exact resolve b8e85 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85
          have b8e9204 : x ≠ (σ y) := by
            first
            | (have i₁ := b8e127 x
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e127
            | exact resolve b8e127 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e9223 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e358 X0 x
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e358
            | exact resolve b8e358 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358
          have b8e9224 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
            intro X0
            first
            | (have i₁ := b8e369 x X0
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e369
            | exact resolve b8e369 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e369
          have b8e9251 : ∀ X0 : G, (σ (σ (M.op X0 X0))) = (τ (τ x)) := by
            intro X0
            first
            | (have i₁ := b8e1258 x X0
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e1258
            | exact resolve b8e1258 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1258
          have b8e9256 : ∀ X0 : G, (σ (M.op X0 X0)) = (τ (τ x)) := by
            intro X0
            first
            | (have i₁ := b8e1274 x X0
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e1274
            | exact resolve b8e1274 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1274
          have b8e9274 : (τ (τ x)) = (σ (τ (τ x))) := by
            first
            | (have i₁ := b8e9251 x
               have i₂ := b8e9256 x
               grind)
            | exact superpose b8e9256 b8e9251
            | exact resolve b8e9251 b8e9256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9251
          have b8e9280 : (σ x) = (σ (τ x)) := by
            first
            | (have i₁ := b8e9223 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e9223
            | exact resolve b8e9223 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9223
          have b8e9289 : (τ x) = (τ (τ x)) := by
            first
            | (have i₁ := b8e9274
               have i₂ := b8e15 (τ x)
               grind)
            | exact superpose b8e15 b8e9274
            | exact resolve b8e9274 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9274
          have b8e9294 : x = (σ x) := by
            first
            | (have i₁ := b8e9280
               have i₂ := b8e15 x
               grind)
            | exact superpose b8e15 b8e9280
            | exact resolve b8e9280 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9280
          have b8e11441 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e20
            | exact resolve b8e20 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11443 : x = (τ x) := by
            first
            | (have i₁ := b8e14 x
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e14
            | exact resolve b8e14 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11444 : ∀ X0 : G, (σ (k x X0)) = (k x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 x X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e19
            | exact resolve b8e19 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11445 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 x
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e19
            | exact resolve b8e19 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e11451 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e39 X0 x
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e39
            | exact resolve b8e39 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39
          have b8e11460 : (σ (k x y)) = (M.op (σ y) x) ∨ x = (σ y) := by
            first
            | (have i₁ := b8e93 x
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e93
            | exact resolve b8e93 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e93
          have b8e11470 : (σ (k x y)) = (M.op (σ y) x) := by
            first
            | (have r₁ := b8e11460
               have r₂ := b8e9204
               grind)
            | exact resolve b8e11460 b8e9204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11460
          have b8e12534 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ x = X0 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e18 X1 X0
               have i₂ := b8e9202 X0
               grind)
            | exact superpose b8e9202 b8e18
            | (have j0 := b8e18 X1 X0
               grind)
            | exact resolve b8e18 b8e9202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9202
          have b8e38422 : ∀ X0 X1 X2 : G, (k (τ X0) (M.op X2 X2)) = (τ (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e432 X1 X0 X2
               have i₂ := b8e43 X1 X0
               grind)
            | exact superpose b8e43 b8e432
            | (have j1 := b8e43 X1 X0
               grind)
            | exact resolve b8e432 b8e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e38567 : ∀ X0 X1 X2 : G, (k (τ X0) (M.op X2 X2)) = (τ (M.op X0 (τ x))) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e38422 X0 X1 X2
               have i₂ := b8e9224 X1
               grind)
            | exact superpose b8e9224 b8e38422
            | (have j0 := b8e38422 X0 X1 X2
               grind)
            | exact resolve b8e38422 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38422
          have b8e38713 : ∀ X0 X1 X2 : G, (k (τ X0) (M.op X2 X2)) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e38567 X0 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e38567
            | (have j0 := b8e38567 X0 X1 X2
               grind)
            | exact resolve b8e38567 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38567
          have b8e38848 : ∀ X0 X1 : G, (k (τ X0) (τ x)) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e38713 X0 X1 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e38713
            | (have j0 := b8e38713 X0 X1 x
               grind)
            | exact resolve b8e38713 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38713
          have b8e38980 : ∀ X0 X1 : G, (τ (k X0 x)) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e38848 X0 X1
               have i₂ := b8e429 x X0
               grind)
            | exact superpose b8e429 b8e38848
            | (have j0 := b8e38848 X0 X1
               grind)
            | exact resolve b8e38848 b8e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38848
          have b8e39078 : ∀ X0 X1 : G, (k (τ X0) x) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e38980 X0 X1
               have i₂ := b8e11451 X0
               grind)
            | exact superpose b8e11451 b8e38980
            | (have j0 := b8e38980 X0 X1
               grind)
            | exact resolve b8e38980 b8e11451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e38980
          have b8e39170 : ∀ X0 : G, (τ x) = X0 ∨ (k (τ X0) x) = (τ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e39078 X0 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e39078
            | (have j0 := b8e39078 X0 x
               grind)
            | exact resolve b8e39078 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39078
          have b8e39251 : ∀ X0 : G, (k (τ X0) x) = (τ (M.op X0 x)) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e39170 X0
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e39170
            | (have j0 := b8e39170 X0
               grind)
            | exact resolve b8e39170 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39170
          have b8e39870 : ∀ X0 X1 X2 : G, (τ (M.op X0 (M.op X1 X1))) = (k (M.op X2 X2) (τ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e503 X1 X2 X0
               have i₂ := b8e18 (M.op X1 X1) X0
               grind)
            | exact superpose b8e18 b8e503
            | (have j1 := b8e18 (M.op X0 X0) X0
               grind)
            | exact resolve b8e503 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e39898 : ∀ X0 X1 : G, (k (M.op X1 X1) (τ (σ y))) = (τ (M.op (σ y) (M.op X0 X0))) ∨ (M.op X0 X0) = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b8e503 X0 X1 (σ y)
               have i₂ := b8e63 (M.op X0 X0)
               grind)
            | exact superpose b8e63 b8e503
            | (have j1 := b8e63 (M.op X0 X0)
               grind)
            | exact resolve b8e503 b8e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e39939 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (σ (τ (k (M.op X0 X0) X1))) (M.op X3 X3)) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e291 (M.op X2 X2) (τ X1) X3
               have i₂ := b8e503 X0 X2 X1
               grind)
            | exact superpose b8e503 b8e291
            | (have j0 := b8e291 (M.op (τ X1) (τ X1)) (τ X1) X2
               grind)
            | exact resolve b8e291 b8e503
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e291 b8e503
          have b8e39999 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (σ (τ (k (M.op X0 X0) X1))) (τ x)) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e39939 X0 X1 X2 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e39939
            | (have j0 := b8e39939 X0 X1 (τ X1) x
               grind)
            | exact resolve b8e39939 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39939
          have b8e40032 : ∀ X0 X1 : G, (k (M.op X1 X1) (τ (σ y))) = (τ (M.op (σ y) (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have j0 := b8e39898 X0 X1
               grind)
            | (have r₁ := b8e39898 X0 X1
               have r₂ := b8e127 X0
               grind)
            | exact resolve b8e39898 b8e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127 b8e39898
          have b8e40055 : ∀ X0 X1 : G, (k (τ x) (τ X0)) = (τ (M.op X0 (M.op X1 X1))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e39870 X0 X1 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e39870
            | (have j0 := b8e39870 X0 X0 x
               grind)
            | exact resolve b8e39870 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39870
          have b8e40194 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (σ (τ (k (M.op X0 X0) X1))) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e39999 X0 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e39999
            | (have j0 := b8e39999 X0 X1 (τ X1)
               grind)
            | exact resolve b8e39999 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39999
          have b8e40227 : ∀ X1 : G, (k (M.op X1 X1) (τ (σ y))) = (τ (M.op (σ y) (τ x))) := by
            intro X1
            first
            | (have i₁ := b8e40032 x X1
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e40032
            | exact resolve b8e40032 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40032
          have b8e40250 : ∀ X0 X1 : G, (k (τ x) (τ X0)) = (τ (M.op X0 (τ x))) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e40055 X0 X1
               have i₂ := b8e9224 X1
               grind)
            | exact superpose b8e9224 b8e40055
            | (have j0 := b8e40055 X0 X0
               grind)
            | exact resolve b8e40055 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40055
          have b8e40378 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (k (M.op X0 X0) X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e40194 X0 X1 X2
               have i₂ := b8e15 (k (M.op X0 X0) X1)
               grind)
            | exact superpose b8e15 b8e40194
            | (have j0 := b8e40194 X0 X1 (τ X1)
               grind)
            | exact resolve b8e40194 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40194
          have b8e40411 : ∀ X1 : G, (k (M.op X1 X1) (τ (σ y))) = (τ (M.op (σ y) x)) := by
            intro X1
            first
            | (have i₁ := b8e40227 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40227
            | exact resolve b8e40227 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40227
          have b8e40434 : ∀ X0 X1 : G, (k x (τ X0)) = (τ (M.op X0 x)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e40250 X0 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40250
            | (have j0 := b8e40250 X0 X0
               grind)
            | exact resolve b8e40250 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40250
          have b8e40561 : ∀ X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (k (τ x) X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e40378 x X1 X2
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e40378
            | (have j0 := b8e40378 x X1 (τ X1)
               grind)
            | exact resolve b8e40378 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40378
          have b8e40594 : ∀ X1 : G, (k (M.op X1 X1) y) = (τ (M.op (σ y) x)) := by
            intro X1
            first
            | (have i₁ := b8e40411 X1
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e40411
            | exact resolve b8e40411 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40411
          have b8e40617 : ∀ X0 X1 : G, (τ x) = X0 ∨ (k x (τ X0)) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e40434 X0 X1
               have i₂ := b8e9224 X0
               grind)
            | exact superpose b8e9224 b8e40434
            | (have j0 := b8e40434 X0 X1
               grind)
            | exact resolve b8e40434 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40434
          have b8e40709 : ∀ X1 X2 : G, (M.op (σ (M.op X2 X2)) (σ (τ X1))) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e40561 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40561
            | (have j0 := b8e40561 X1 (τ X1)
               grind)
            | exact resolve b8e40561 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40561
          have b8e40741 : (k (τ x) y) = (τ (M.op (σ y) x)) := by
            first
            | (have i₁ := b8e40594 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e40594
            | exact resolve b8e40594 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40594
          have b8e40763 : ∀ X0 X1 : G, x = X0 ∨ (k x (τ X0)) = (τ (M.op X0 x)) ∨ (M.op X1 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e40617 X0 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40617
            | (have j0 := b8e40617 X0 X1
               grind)
            | exact resolve b8e40617 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40617
          have b8e40849 : ∀ X1 X2 : G, (M.op (σ (M.op X2 X2)) X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e40709 X1 X2
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e40709
            | (have j0 := b8e40709 X1 (τ X1)
               grind)
            | exact resolve b8e40709 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40709
          have b8e40879 : (k x y) = (τ (M.op (σ y) x)) := by
            first
            | (have i₁ := b8e40741
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40741
            | exact resolve b8e40741 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40741
          have b8e40893 : ∀ X0 : G, (τ x) = X0 ∨ x = X0 ∨ (k x (τ X0)) = (τ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e40763 X0 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e40763
            | (have j0 := b8e40763 X0 x
               grind)
            | exact resolve b8e40763 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40763
          have b8e40974 : ∀ X1 X2 : G, (M.op (τ (τ x)) X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e40849 X1 X2
               have i₂ := b8e9256 X2
               grind)
            | exact superpose b8e9256 b8e40849
            | (have j0 := b8e40849 X1 (τ X1)
               grind)
            | exact resolve b8e40849 b8e9256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40849
          have b8e41010 : ∀ X0 : G, x = X0 ∨ x = X0 ∨ (k x (τ X0)) = (τ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b8e40893 X0
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e40893
            | (have j0 := b8e40893 X0
               grind)
            | exact resolve b8e40893 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40893
          have b8e41011 : ∀ X0 : G, (k x (τ X0)) = (τ (M.op X0 x)) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b8e41010 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41010
          have b8e41082 : ∀ X1 X2 : G, (M.op (τ x) X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e40974 X1 X2
               have i₂ := b8e9289
               grind)
            | exact superpose b8e9289 b8e40974
            | (have j0 := b8e40974 X1 (τ X1)
               grind)
            | exact resolve b8e40974 b8e9289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40974
          have b8e41158 : ∀ X1 X2 : G, (M.op x X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op (τ X1) (τ X1))) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41082 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e41082
            | (have j0 := b8e41082 X1 (τ X1)
               grind)
            | exact resolve b8e41082 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41082
          have b8e41227 : ∀ X1 X2 : G, (M.op X1 X1) = (σ (τ X1)) ∨ (M.op x X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41158 X1 X2
               have i₂ := b8e41 X1
               grind)
            | exact superpose b8e41 b8e41158
            | (have j0 := b8e41158 X1 X2
               grind)
            | exact resolve b8e41158 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e41158
          have b8e41279 : ∀ X1 X2 : G, (M.op X1 X1) = X1 ∨ (M.op x X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41227 X1 X2
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e41227
            | (have j0 := b8e41227 X1 X2
               grind)
            | exact resolve b8e41227 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41227
          have b8e41315 : ∀ X1 X2 : G, (τ x) = X1 ∨ (M.op x X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41279 X1 X2
               have i₂ := b8e9224 X1
               grind)
            | exact superpose b8e9224 b8e41279
            | (have j0 := b8e41279 X1 X2
               grind)
            | exact resolve b8e41279 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41279
          have b8e41345 : ∀ X1 X2 : G, x = X1 ∨ (M.op x X1) = (M.op (k x X1) x) ∨ (σ (τ X1)) = (σ (M.op X2 X2)) := by
            intro X1 X2
            first
            | (have i₁ := b8e41315 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e41315
            | (have j0 := b8e41315 X1 X2
               grind)
            | exact resolve b8e41315 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41315
          have b8e41370 : ∀ X1 : G, (σ (τ X1)) = (τ (τ x)) ∨ x = X1 ∨ (M.op x X1) = (M.op (k x X1) x) := by
            intro X1
            first
            | (have i₁ := b8e41345 X1 x
               have i₂ := b8e9256 x
               grind)
            | exact superpose b8e9256 b8e41345
            | (have j0 := b8e41345 X1 x
               grind)
            | exact resolve b8e41345 b8e9256
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9256 b8e41345
          have b8e41384 : ∀ X1 : G, (σ (τ X1)) = (τ x) ∨ x = X1 ∨ (M.op x X1) = (M.op (k x X1) x) := by
            intro X1
            first
            | (have i₁ := b8e41370 X1
               have i₂ := b8e9289
               grind)
            | exact superpose b8e9289 b8e41370
            | (have j0 := b8e41370 X1
               grind)
            | exact resolve b8e41370 b8e9289
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9289 b8e41370
          have b8e41396 : ∀ X1 : G, x = (σ (τ X1)) ∨ x = X1 ∨ (M.op x X1) = (M.op (k x X1) x) := by
            intro X1
            first
            | (have i₁ := b8e41384 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e41384
            | (have j0 := b8e41384 X1
               grind)
            | exact resolve b8e41384 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41384
          have b8e41401 : ∀ X1 : G, x = X1 ∨ x = X1 ∨ (M.op x X1) = (M.op (k x X1) x) := by
            intro X1
            first
            | (have i₁ := b8e41396 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e41396
            | (have j0 := b8e41396 X1
               grind)
            | exact resolve b8e41396 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41396
          have b8e41402 : ∀ X1 : G, (M.op x X1) = (M.op (k x X1) x) ∨ x = X1 := by
            intro X1
            first
            | (have j0 := b8e41401 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41401
          have b8e42398 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (σ (M.op y (M.op X0 X0))) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
            intro X0 X1
            first
            | (have i₁ := b8e1199 X1 X0
               have i₂ := b8e18 (M.op X0 X0) y
               grind)
            | exact superpose b8e18 b8e1199
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | exact resolve b8e1199 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42524 : ∀ X0 X1 X2 X3 : G, (σ (k (M.op X1 X1) (k (M.op X2 X2) y))) = (k (M.op X3 X3) (M.op (σ y) (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e368 X3 X1 (k (M.op X2 X2) y)
               have i₂ := b8e1199 X0 X2
               grind)
            | exact superpose b8e1199 b8e368
            | exact resolve b8e368 b8e1199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e42586 : ∀ X1 X2 X3 : G, (σ (k (M.op X1 X1) (k (M.op X2 X2) y))) = (k (M.op X3 X3) (M.op (σ y) (τ x))) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e42524 x X1 X2 X3
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e42524
            | exact resolve b8e42524 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42524
          have b8e42680 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (σ (M.op y (M.op X0 X0))) ∨ (M.op X0 X0) = y := by
            intro X0 X1
            first
            | (have j0 := b8e42398 X0 X1
               grind)
            | (have r₁ := b8e42398 X0 X1
               have r₂ := b8e22
               grind)
            | (have r₁ := b8e42398 y X1
               have r₂ := b8e22
               grind)
            | exact resolve b8e42398 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42398
          have b8e42737 : ∀ X1 X2 X3 : G, (σ (k (M.op X1 X1) (k (M.op X2 X2) y))) = (k (M.op X3 X3) (M.op (σ y) x)) := by
            intro X1 X2 X3
            first
            | (have i₁ := b8e42586 X1 X2 X3
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e42586
            | exact resolve b8e42586 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42586
          have b8e42829 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (σ (M.op y (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have j0 := b8e42680 X0 X1
               grind)
            | (have r₁ := b8e42680 X0 X1
               have r₂ := b8e130 X0
               grind)
            | exact resolve b8e42680 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130 b8e42680
          have b8e42884 : ∀ X1 X2 : G, (σ (k (M.op X1 X1) (k (M.op X2 X2) y))) = (k (τ x) (M.op (σ y) x)) := by
            intro X1 X2
            first
            | (have i₁ := b8e42737 X1 X2 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e42737
            | exact resolve b8e42737 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42737
          have b8e42974 : ∀ X1 : G, (M.op (σ y) (M.op X1 X1)) = (σ (M.op y (τ x))) := by
            intro X1
            first
            | (have i₁ := b8e42829 x X1
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e42829
            | exact resolve b8e42829 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42829
          have b8e43013 : ∀ X1 X2 : G, (σ (k (M.op X1 X1) (k (M.op X2 X2) y))) = (k x (M.op (σ y) x)) := by
            intro X1 X2
            first
            | (have i₁ := b8e42884 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e42884
            | exact resolve b8e42884 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42884
          have b8e43101 : ∀ X1 : G, (σ (M.op y x)) = (M.op (σ y) (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b8e42974 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e42974
            | exact resolve b8e42974 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e42974
          have b8e43133 : ∀ X1 : G, (k x (M.op (σ y) x)) = (σ (k (M.op X1 X1) (k (τ x) y))) := by
            intro X1
            first
            | (have i₁ := b8e43013 X1 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e43013
            | exact resolve b8e43013 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43013
          have b8e43197 : (σ (M.op y x)) = (M.op (σ y) (τ x)) := by
            first
            | (have i₁ := b8e43101 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e43101
            | exact resolve b8e43101 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43101
          have b8e43226 : ∀ X1 : G, (k x (M.op (σ y) x)) = (σ (k (M.op X1 X1) (k x y))) := by
            intro X1
            first
            | (have i₁ := b8e43133 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e43133
            | exact resolve b8e43133 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43133
          have b8e43278 : (σ (M.op y x)) = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e43197
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e43197
            | exact resolve b8e43197 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43197
          have b8e43299 : (k x (M.op (σ y) x)) = (σ (k (τ x) (k x y))) := by
            first
            | (have i₁ := b8e43226 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e43226
            | exact resolve b8e43226 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43226
          have b8e43355 : (k x (M.op (σ y) x)) = (k x (σ (k x y))) := by
            first
            | (have i₁ := b8e43299
               have i₂ := b8e26 x (k x y)
               grind)
            | exact superpose b8e26 b8e43299
            | exact resolve b8e43299 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43299
          have b8e43392 : (k x (M.op (σ y) x)) = (σ (k x (k x y))) := by
            first
            | (have i₁ := b8e43355
               have i₂ := b8e11444 (k x y)
               grind)
            | exact superpose b8e11444 b8e43355
            | exact resolve b8e43355 b8e11444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43355
          have b8e58358 : (M.op y x) = (τ (M.op (σ y) x)) := by
            first
            | (have i₁ := b8e14 (M.op y x)
               have i₂ := b8e43278
               grind)
            | exact superpose b8e43278 b8e14
            | exact resolve b8e14 b8e43278
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43278
          have b8e63392 : (M.op y x) = (k x y) := by
            first
            | (have i₁ := b8e40879
               have i₂ := b8e58358
               grind)
            | exact superpose b8e58358 b8e40879
            | exact resolve b8e40879 b8e58358
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40879
          have b8e98128 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (M.op X2 X2) (σ (k (M.op X0 X0) y))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e1689 (σ y) (M.op X0 X0) X2
               have i₂ := b8e1199 X0 X1
               grind)
            | exact superpose b8e1199 b8e1689
            | exact resolve b8e1689 b8e1199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1199
          have b8e98188 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X1)) = (k (M.op X3 X3) (σ (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op X2 X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e368 X3 X2 (M.op X1 X0)
               have i₂ := b8e1689 X1 X0 X2
               grind)
            | exact superpose b8e1689 b8e368
            | (have j1 := b8e1689 X1 X0 X2
               grind)
            | exact resolve b8e368 b8e1689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368 b8e1689
          have b8e98302 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k (τ x) (σ (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98188 X0 X1 X2 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e98188
            | (have j0 := b8e98188 X0 X1 X2 x
               grind)
            | exact resolve b8e98188 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98188
          have b8e98321 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (M.op X2 X2) (σ (k (τ x) y))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98128 X0 X1 X2
               have i₂ := b8e9224 X0
               grind)
            | exact superpose b8e9224 b8e98128
            | (have j0 := b8e98128 X0 X1 X2
               grind)
            | exact resolve b8e98128 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98128
          have b8e98371 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (k x (σ (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98302 X0 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e98302
            | (have j0 := b8e98302 X0 X1 X2
               grind)
            | exact resolve b8e98302 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98302
          have b8e98389 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (M.op X2 X2) (k x (σ y))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98321 X0 X1 X2
               have i₂ := b8e26 x y
               grind)
            | exact superpose b8e26 b8e98321
            | (have j0 := b8e98321 X0 X1 X2
               grind)
            | exact resolve b8e98321 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98321
          have b8e98437 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (σ (k x (M.op X1 X0))) ∨ (M.op X1 X0) = (M.op X2 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98371 X0 X1 X2
               have i₂ := b8e11444 (M.op X1 X0)
               grind)
            | exact superpose b8e11444 b8e98371
            | (have j0 := b8e98371 X0 X1 X2
               grind)
            | exact resolve b8e98371 b8e11444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98371
          have b8e98455 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (M.op X2 X2) (σ (k x y))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98389 X0 X1 X2
               have i₂ := b8e11444 y
               grind)
            | exact superpose b8e11444 b8e98389
            | (have j0 := b8e98389 X0 X1 X2
               grind)
            | exact resolve b8e98389 b8e11444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98389
          have b8e98483 : ∀ X0 X1 : G, (M.op X1 X0) = (τ x) ∨ (σ (M.op X0 X1)) = (σ (k x (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e98437 X0 X1 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e98437
            | (have j0 := b8e98437 X0 X1 x
               grind)
            | exact resolve b8e98437 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98437
          have b8e98488 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (M.op X2 X2) (M.op (σ y) x)) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98455 X0 X1 X2
               have i₂ := b8e11470
               grind)
            | exact superpose b8e11470 b8e98455
            | (have j0 := b8e98455 X0 X1 X2
               grind)
            | exact resolve b8e98455 b8e11470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98455
          have b8e98511 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (σ (k x (M.op X1 X0))) ∨ (M.op X1 X0) = x := by
            intro X0 X1
            first
            | (have i₁ := b8e98483 X0 X1
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e98483
            | (have j0 := b8e98483 X0 X1
               grind)
            | exact resolve b8e98483 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98483
          have b8e98516 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k (τ x) (M.op (σ y) x)) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98488 X0 X1 X2
               have i₂ := b8e9224 X2
               grind)
            | exact superpose b8e9224 b8e98488
            | (have j0 := b8e98488 X0 X1 X2
               grind)
            | exact resolve b8e98488 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98488
          have b8e98535 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (k x (M.op (σ y) x)) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98516 X0 X1 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e98516
            | (have j0 := b8e98516 X0 X1 X2
               grind)
            | exact resolve b8e98516 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98516
          have b8e98548 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (σ (k x (k x y))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98535 X0 X1 X2
               have i₂ := b8e43392
               grind)
            | exact superpose b8e43392 b8e98535
            | (have j0 := b8e98535 X0 X1 X2
               grind)
            | exact resolve b8e98535 b8e43392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43392 b8e98535
          have b8e98557 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (σ y)) = (σ (k x (M.op y x))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e98548 X0 X1 X2
               have i₂ := b8e63392
               grind)
            | exact superpose b8e63392 b8e98548
            | (have j0 := b8e98548 X0 X1 X2
               grind)
            | exact resolve b8e98548 b8e63392
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63392 b8e98548
          have b8e98565 : ∀ X0 X2 : G, (M.op (τ x) (σ y)) = (σ (k x (M.op y x))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X2
            first
            | (have i₁ := b8e98557 X0 x X2
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e98557
            | (have j0 := b8e98557 X0 x X2
               grind)
            | exact resolve b8e98557 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98557
          have b8e98566 : ∀ X0 X2 : G, (M.op x (σ y)) = (σ (k x (M.op y x))) ∨ (M.op X2 X2) = (σ (k (M.op X0 X0) y)) := by
            intro X0 X2
            first
            | (have i₁ := b8e98565 X0 X2
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e98565
            | (have j0 := b8e98565 X0 X2
               grind)
            | exact resolve b8e98565 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98565
          have b8e98567 : ∀ X2 : G, (M.op X2 X2) = (σ (k (τ x) y)) ∨ (M.op x (σ y)) = (σ (k x (M.op y x))) := by
            intro X2
            first
            | (have i₁ := b8e98566 x X2
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e98566
            | exact resolve b8e98566 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98566
          have b8e98568 : ∀ X2 : G, (M.op X2 X2) = (k x (σ y)) ∨ (M.op x (σ y)) = (σ (k x (M.op y x))) := by
            intro X2
            first
            | (have i₁ := b8e98567 X2
               have i₂ := b8e26 x y
               grind)
            | exact superpose b8e26 b8e98567
            | exact resolve b8e98567 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98567
          have b8e98569 : ∀ X2 : G, (M.op X2 X2) = (σ (k x y)) ∨ (M.op x (σ y)) = (σ (k x (M.op y x))) := by
            intro X2
            first
            | (have i₁ := b8e98568 X2
               have i₂ := b8e11444 y
               grind)
            | exact superpose b8e11444 b8e98568
            | exact resolve b8e98568 b8e11444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11444 b8e98568
          have b8e98570 : ∀ X2 : G, (M.op X2 X2) = (M.op (σ y) x) ∨ (M.op x (σ y)) = (σ (k x (M.op y x))) := by
            intro X2
            first
            | (have i₁ := b8e98569 X2
               have i₂ := b8e11470
               grind)
            | exact superpose b8e11470 b8e98569
            | exact resolve b8e98569 b8e11470
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11470 b8e98569
          have b8e98571 : (τ x) = (M.op (σ y) x) ∨ (M.op x (σ y)) = (σ (k x (M.op y x))) := by
            first
            | (have i₁ := b8e98570 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e98570
            | exact resolve b8e98570 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98570
          have b8e98572 : (M.op x (σ y)) = (σ (k x (M.op y x))) ∨ x = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e98571
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e98571
            | exact resolve b8e98571 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98571
          have b8e115198 : ∀ X0 : G, (k x (τ X0)) = (k (τ X0) x) ∨ x = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e39251 X0
               have i₂ := b8e41011 X0
               grind)
            | exact superpose b8e41011 b8e39251
            | (have j0 := b8e39251 X0
               have j1 := b8e41011 X0
               grind)
            | exact resolve b8e39251 b8e41011
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39251 b8e41011
          have b8e115240 : ∀ X0 : G, (k x (τ X0)) = (k (τ X0) x) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b8e115198 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115198
          have b8e129442 : ∀ X0 : G, (k X0 (σ x)) = (σ (k x (τ X0))) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e26 X0 x
               have i₂ := b8e115240 X0
               grind)
            | exact superpose b8e115240 b8e26
            | (have j1 := b8e115240 X0
               grind)
            | exact resolve b8e26 b8e115240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115240
          have b8e129498 : ∀ X0 : G, (k X0 (σ x)) = (k (σ x) X0) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e129442 X0
               have i₂ := b8e27 X0 x
               grind)
            | exact superpose b8e27 b8e129442
            | (have j0 := b8e129442 X0
               grind)
            | exact resolve b8e129442 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129442
          have b8e129537 : ∀ X0 : G, (k X0 x) = (k x X0) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e129498 X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e129498
            | (have j0 := b8e129498 X0
               grind)
            | exact resolve b8e129498 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129498
          have b8e130133 : ∀ X0 : G, (k X0 (σ x)) = (σ (k x (τ X0))) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e26 X0 x
               have i₂ := b8e129537 (τ X0)
               grind)
            | exact superpose b8e129537 b8e26
            | (have j1 := b8e129537 (τ X0)
               grind)
            | exact resolve b8e26 b8e129537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e130153 : ∀ X0 : G, (M.op x X0) = (M.op (k X0 x) x) ∨ x = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e41402 X0
               have i₂ := b8e129537 X0
               grind)
            | (have i₁ := b8e41402 x
               have i₂ := b8e129537 x
               grind)
            | exact superpose b8e129537 b8e41402
            | (have j0 := b8e41402 X0
               have j1 := b8e129537 X0
               grind)
            | exact resolve b8e41402 b8e129537
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41402 b8e129537
          have b8e130176 : ∀ X0 : G, (M.op x X0) = (M.op (k X0 x) x) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b8e130153 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130153
          have b8e130253 : ∀ X0 : G, (k X0 (σ x)) = (k (σ x) X0) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e130133 X0
               have i₂ := b8e27 X0 x
               grind)
            | exact superpose b8e27 b8e130133
            | (have j0 := b8e130133 X0
               grind)
            | exact resolve b8e130133 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130133
          have b8e130295 : ∀ X0 : G, (k X0 x) = (k x X0) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e130253 X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e130253
            | (have j0 := b8e130253 X0
               grind)
            | exact resolve b8e130253 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130253
          have b8e131394 : ∀ X0 : G, (k X0 (σ x)) = (σ (k x (τ X0))) ∨ x = (τ (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 x
               have i₂ := b8e130295 (τ X0)
               grind)
            | exact superpose b8e130295 b8e26
            | (have j1 := b8e130295 (τ X0)
               grind)
            | exact resolve b8e26 b8e130295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130295
          have b8e131451 : ∀ X0 : G, (k X0 (σ x)) = (k (σ x) X0) ∨ x = (τ (τ X0)) := by
            intro X0
            first
            | (have i₁ := b8e131394 X0
               have i₂ := b8e27 X0 x
               grind)
            | exact superpose b8e27 b8e131394
            | (have j0 := b8e131394 X0
               grind)
            | exact resolve b8e131394 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e131394
          have b8e131496 : ∀ X0 : G, x = (τ (τ X0)) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e131451 X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e131451
            | (have j0 := b8e131451 X0
               grind)
            | exact resolve b8e131451 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131451
          have b8e142334 : ∀ X0 : G, (M.op x (σ X0)) = (M.op (σ (k X0 x)) x) ∨ (σ X0) = x := by
            intro X0
            first
            | (have i₁ := b8e130176 (σ X0)
               have i₂ := b8e11445 X0
               grind)
            | exact superpose b8e11445 b8e130176
            | (have j0 := b8e130176 (σ X0)
               grind)
            | exact resolve b8e130176 b8e11445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11445 b8e130176
          have b8e144664 : ∀ X0 X1 X2 : G, (k x (M.op X1 X1)) = (τ (k (τ X0) (M.op X2 X2))) ∨ (k X0 x) = (k x X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e432 X2 (τ X0) X1
               have i₂ := b8e131496 X0
               grind)
            | exact superpose b8e131496 b8e432
            | (have j1 := b8e131496 X0
               grind)
            | exact resolve b8e432 b8e131496
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e432 b8e131496
          have b8e144693 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (τ (k (τ X0) (τ x))) ∨ (k X0 x) = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e144664 X0 X1 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e144664
            | (have j0 := b8e144664 X0 X1 x
               grind)
            | exact resolve b8e144664 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144664
          have b8e144788 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (τ (τ (k X0 x))) ∨ (k X0 x) = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e144693 X0 X1
               have i₂ := b8e429 x X0
               grind)
            | exact superpose b8e429 b8e144693
            | (have j0 := b8e144693 X0 X1
               grind)
            | exact resolve b8e144693 b8e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e429 b8e144693
          have b8e144863 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (τ (k (τ X0) x)) ∨ (k X0 x) = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e144788 X0 X1
               have i₂ := b8e11451 X0
               grind)
            | exact superpose b8e11451 b8e144788
            | (have j0 := b8e144788 X0 X1
               grind)
            | exact resolve b8e144788 b8e11451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144788
          have b8e144918 : ∀ X0 X1 : G, (k x (M.op X1 X1)) = (k (τ (τ X0)) x) ∨ (k X0 x) = (k x X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e144863 X0 X1
               have i₂ := b8e11451 (τ X0)
               grind)
            | exact superpose b8e11451 b8e144863
            | (have j0 := b8e144863 X0 X1
               grind)
            | exact resolve b8e144863 b8e11451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11451 b8e144863
          have b8e144935 : ∀ X0 : G, (k x (τ x)) = (k (τ (τ X0)) x) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e144918 X0 x
               have i₂ := b8e9224 x
               grind)
            | exact superpose b8e9224 b8e144918
            | (have j0 := b8e144918 X0 x
               grind)
            | exact resolve b8e144918 b8e9224
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9224 b8e144918
          have b8e144946 : ∀ X0 : G, (k x x) = (k (τ (τ X0)) x) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e144935 X0
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e144935
            | (have j0 := b8e144935 X0
               grind)
            | exact resolve b8e144935 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144935
          have b8e144955 : ∀ X0 : G, (M.op x x) = (k (τ (τ X0)) x) ∨ (k X0 x) = (k x X0) := by
            intro X0
            grind
          clear b8e144946
          have b8e144962 : ∀ X0 : G, x = (k (τ (τ X0)) x) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e144955 X0
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e144955
            | (have j0 := b8e144955 X0
               grind)
            | exact resolve b8e144955 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144955
          have b8e273310 : ∀ X0 : G, (σ x) = (k (τ X0) (σ x)) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e26 (τ X0) x
               have i₂ := b8e144962 X0
               grind)
            | exact superpose b8e144962 b8e26
            | (have j1 := b8e144962 X0
               grind)
            | exact resolve b8e26 b8e144962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144962
          have b8e273354 : ∀ X0 : G, x = (k (τ X0) x) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e273310 X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e273310
            | (have j0 := b8e273310 X0
               grind)
            | exact resolve b8e273310 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273310
          have b8e273827 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ (k X0 x) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 x
               have i₂ := b8e273354 X0
               grind)
            | exact superpose b8e273354 b8e26
            | (have j1 := b8e273354 X0
               grind)
            | exact resolve b8e26 b8e273354
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e273354
          have b8e273881 : ∀ X0 : G, (k X0 x) = (k x X0) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b8e273827 X0
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e273827
            | (have j0 := b8e273827 X0
               grind)
            | exact resolve b8e273827 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273827
          have b8e274252 : ∀ X0 : G, x ≠ (k x X0) ∨ x = (k X0 x) := by
            intro X0
            first
            | (have j0 := b8e273881 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e273881
          have b8e274494 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k X0 x) ∨ x = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b8e274252 X0
               have i₂ := b8e12534 X0 x
               grind)
            | exact superpose b8e12534 b8e274252
            | (have j0 := b8e274252 X0
               have j1 := b8e12534 (k X0 x) x
               grind)
            | (have r₁ := b8e274252 X0
               have r₂ := b8e12534 (k x X0) x
               grind)
            | (have r₁ := b8e274252 X0
               have r₂ := b8e12534 x (k x X0)
               grind)
            | (have r₁ := b8e274252 X0
               have r₂ := b8e12534 (k x X0) x
               grind)
            | exact resolve b8e274252 b8e12534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12534 b8e274252
          have b8e274506 : ∀ X0 : G, x ≠ (M.op X0 x) ∨ x = (k X0 x) ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b8e274494 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274494
          have b8e575547 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (M.op y x) ∨ x = (M.op (σ y) x) := by
            first
            | (have i₁ := b8e98511 x y
               have i₂ := b8e98572
               grind)
            | exact superpose b8e98572 b8e98511
            | (have j0 := b8e98511 x y
               grind)
            | exact resolve b8e98511 b8e98572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e98511 b8e98572
          have b8e575550 : x = (M.op (σ y) x) ∨ x = (M.op y x) := by
            first
            | (have r₁ := b8e575547
               have r₂ := b8e11441
               grind)
            | exact resolve b8e575547 b8e11441
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e575547
          have b8e575566 : (M.op y x) = (τ x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e58358
               have i₂ := b8e575550
               grind)
            | exact superpose b8e575550 b8e58358
            | exact resolve b8e58358 b8e575550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58358 b8e575550
          have b8e575775 : x = (M.op y x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e575566
               have i₂ := b8e11443
               grind)
            | exact superpose b8e11443 b8e575566
            | exact resolve b8e575566 b8e11443
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11443 b8e575566
          have b8e575776 : x = (M.op y x) := by grind
          clear b8e575775
          have b8e575931 : x ≠ x ∨ x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e274506 y
               have i₂ := b8e575776
               grind)
            | exact superpose b8e575776 b8e274506
            | (have j0 := b8e274506 y
               grind)
            | (have r₁ := b8e274506 y
               have r₂ := b8e575776
               grind)
            | exact resolve b8e274506 b8e575776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e274506
          have b8e576057 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e9190 x y
               have i₂ := b8e575776
               grind)
            | exact superpose b8e575776 b8e9190
            | exact resolve b8e9190 b8e575776
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9190 b8e575776
          have b8e576067 : x = (k y x) ∨ x = y := by grind
          clear b8e575931
          have b8e576072 : x = (M.op x y) := by
            first
            | (have i₁ := b8e576057
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e576057
            | exact resolve b8e576057 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e576057
          have b8e576184 : x = (k y x) := by
            first
            | (have r₁ := b8e576067
               have r₂ := b8e21
               grind)
            | exact resolve b8e576067 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e576067
          have b8e577003 : (σ x) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e11441
               have i₂ := b8e576072
               grind)
            | exact superpose b8e576072 b8e11441
            | exact resolve b8e11441 b8e576072
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11441 b8e576072
          have b8e577092 : x ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e577003
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e577003
            | exact resolve b8e577003 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e577003
          have b8e577198 : (M.op x (σ y)) = (M.op (σ x) x) ∨ x = (σ y) := by
            first
            | (have i₁ := b8e142334 y
               have i₂ := b8e576184
               grind)
            | exact superpose b8e576184 b8e142334
            | (have j0 := b8e142334 y
               grind)
            | exact resolve b8e142334 b8e576184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142334 b8e576184
          have b8e577584 : (M.op x (σ y)) = (M.op (σ x) x) := by
            first
            | (have r₁ := b8e577198
               have r₂ := b8e9204
               grind)
            | exact resolve b8e577198 b8e9204
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9204 b8e577198
          have b8e577770 : (M.op x x) = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e577584
               have i₂ := b8e9294
               grind)
            | exact superpose b8e9294 b8e577584
            | exact resolve b8e577584 b8e9294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e9294 b8e577584
          have b8e577941 : x = (M.op x (σ y)) := by
            first
            | (have i₁ := b8e577770
               have i₂ := b8e8985
               grind)
            | exact superpose b8e8985 b8e577770
            | exact resolve b8e577770 b8e8985
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8985 b8e577770
          have b8e578085 : False := by grind
          exact b8e578085
