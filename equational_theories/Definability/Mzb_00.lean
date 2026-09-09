import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_x_pxy_Equation1496 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
    · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op x x) := by grind
        have b0e21 : (σ y) = (M.op (σ x) (σ x)) := by grind
        have b0e22 : x = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e38 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 x x X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 y y X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e48 : x = (M.op y (M.op x y)) := by
          first
          | (have i₁ := b0e38 x
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e38
          | exact resolve b0e38 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e61 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 (M.op x y) y X0
             have i₂ := b0e48
             grind)
          | exact superpose b0e48 b0e12
          | exact resolve b0e12 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48
        have b0e62 : y = (M.op x y) := by
          first
          | (have i₁ := b0e61 x
             have i₂ := b0e39 x
             grind)
          | exact superpose b0e39 b0e61
          | exact resolve b0e61 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39 b0e61
        have b0e89 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 y x X0
             have i₂ := b0e62
             grind)
          | exact superpose b0e62 b0e12
          | exact resolve b0e12 b0e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e62
        have b0e90 : x = y := by
          first
          | (have i₁ := b0e89 x
             have i₂ := b0e38 x
             grind)
          | exact superpose b0e38 b0e89
          | exact resolve b0e89 b0e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e38 b0e89
        have b0e107 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e90
             grind)
          | exact superpose b0e90 b0e19
          | exact resolve b0e19 b0e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e90
        have b0e117 : (σ y) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e107
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e107
          | exact resolve b0e107 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e107
        have b0e120 : False := by grind
        exact b0e120
      · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e21 : y = (M.op x x) := by grind
          have b1e23 : x ≠ (M.op y y) := by grind
          have b1e24 : y = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e38 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b1e13 x y X0
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e41 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X0 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e84 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b1e38 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e38
            | exact resolve b1e38 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e88 : x = (M.op y x) := by
            first
            | (have i₁ := b1e38 y
               have i₂ := b1e84
               grind)
            | exact superpose b1e84 b1e38
            | exact resolve b1e38 b1e84
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e84
          have b1e93 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e41 (M.op X1 X0) (M.op X1 (M.op X2 X2))
               have i₂ := b1e13 X0 X1 X2
               grind)
            | exact superpose b1e13 b1e41
            | exact resolve b1e41 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e98 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) y)) := by
            intro X0 X1
            first
            | (have i₁ := b1e41 (M.op X1 X0) (M.op X1 y)
               have i₂ := b1e41 X1 X0
               grind)
            | exact superpose b1e41 b1e41
            | exact resolve b1e41 b1e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e115 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
            intro X1 X2
            first
            | (have i₁ := b1e93 x X1 X2
               have i₂ := b1e98 x X1
               grind)
            | exact superpose b1e98 b1e93
            | exact resolve b1e93 b1e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e93 b1e98
          have b1e119 : x = y := by
            first
            | (have i₁ := b1e24
               have i₂ := b1e88
               grind)
            | exact superpose b1e88 b1e24
            | exact resolve b1e24 b1e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e120 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b1e41 y x
               have i₂ := b1e88
               grind)
            | exact superpose b1e88 b1e41
            | exact resolve b1e41 b1e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41 b1e88
          have b1e124 : x = (M.op x y) := by
            first
            | (have i₁ := b1e120
               have i₂ := b1e115 x y
               grind)
            | exact superpose b1e115 b1e120
            | exact resolve b1e120 b1e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e115 b1e120
          have b1e126 : x = (M.op x x) := by
            first
            | (have i₁ := b1e124
               have i₂ := b1e119
               grind)
            | exact superpose b1e119 b1e124
            | exact resolve b1e124 b1e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e124
          have b1e139 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e119
               grind)
            | exact superpose b1e119 b1e23
            | exact resolve b1e23 b1e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e119
          have b1e153 : False := by grind
          exact b1e153
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op x x) := by grind
          have b2e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b2e23 : x ≠ (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e37 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b2e13 x x X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13 X1 X0 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e43 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
               have i₂ := b2e13 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e46 : x = (M.op y (M.op x (σ y))) := by
            first
            | (have i₁ := b2e37 (σ x)
               have i₂ := b2e22
               grind)
            | exact superpose b2e22 b2e37
            | exact resolve b2e37 b2e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e47 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b2e37 x
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e37
            | exact resolve b2e37 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37
          have b2e54 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b2e13 (M.op x y) y X0
               have i₂ := b2e47
               grind)
            | exact superpose b2e47 b2e13
            | exact resolve b2e13 b2e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e47
          have b2e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X0 X1
               have i₂ := b2e18 (σ X0) (σ X1)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X0) (σ X1)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op X1 X0)) = X2 ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X3 X0) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 X2 X1 X3
               have i₂ := b2e18 X3 X0
               grind)
            | (have i₁ := b2e13 X0 X1 X2
               have i₂ := b2e18 X0 (M.op X2 X2)
               grind)
            | exact superpose b2e18 b2e13
            | (have j1 := b2e18 X3 X0
               grind)
            | exact resolve b2e13 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e74 : ∀ X0 : G, (M.op x (σ y)) = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b2e13 (M.op x (σ y)) y X0
               have i₂ := b2e46
               grind)
            | exact superpose b2e46 b2e13
            | exact resolve b2e13 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e75 : (M.op x y) = (M.op x (σ y)) := by
            first
            | (have i₁ := b2e74 x
               have i₂ := b2e54 x
               grind)
            | exact superpose b2e54 b2e74
            | exact resolve b2e74 b2e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e54 b2e74
          have b2e77 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e40 (M.op X1 X0) (M.op X1 (M.op X2 X2))
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e40
            | exact resolve b2e40 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e78 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) y)) := by
            intro X0 X1
            first
            | (have i₁ := b2e40 (M.op X1 X0) (M.op X1 y)
               have i₂ := b2e40 X1 X0
               grind)
            | exact superpose b2e40 b2e40
            | exact resolve b2e40 b2e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e94 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
            intro X1 X2
            first
            | (have i₁ := b2e77 x X1 X2
               have i₂ := b2e78 x X1
               grind)
            | exact superpose b2e78 b2e77
            | exact resolve b2e77 b2e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e77 b2e78
          have b2e98 : ∀ X0 : G, (σ y) = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b2e13 (σ y) x X0
               have i₂ := b2e75
               grind)
            | exact superpose b2e75 b2e13
            | exact resolve b2e13 b2e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e99 : y = (σ y) := by
            first
            | (have i₁ := b2e98 x
               have i₂ := b2e13 y x x
               grind)
            | exact superpose b2e13 b2e98
            | exact resolve b2e98 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e98
          have b2e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k X0 (τ X1))
               have i₂ := b2e30 X1 X0
               grind)
            | exact superpose b2e30 b2e14
            | exact resolve b2e14 b2e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e112 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e20
            | exact resolve b2e20 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e115 : y = (τ y) := by
            first
            | (have i₁ := b2e14 y
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e14
            | exact resolve b2e14 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e43 X0 (M.op X1 X1) (M.op X1 X1)
               have i₂ := b2e43 (M.op X1 X1) X1 X0
               grind)
            | exact superpose b2e43 b2e43
            | exact resolve b2e43 b2e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e243 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e40 X1 X1
               have i₂ := b2e181 X1 X0
               grind)
            | (have i₁ := b2e40 X1 X1
               have i₂ := b2e181 X0 X1
               grind)
            | exact superpose b2e181 b2e40
            | exact resolve b2e40 b2e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e255 : ∀ X0 : G, (M.op X0 X0) = y := by
            intro X0
            first
            | (have i₁ := b2e21
               have i₂ := b2e181 x X0
               grind)
            | (have i₁ := b2e21
               have i₂ := b2e181 X0 x
               grind)
            | exact superpose b2e181 b2e21
            | exact resolve b2e21 b2e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e181
          have b2e265 : ∀ X1 : G, (M.op y (M.op X1 y)) = X1 := by
            intro X1
            first
            | (have i₁ := b2e243 x X1
               have i₂ := b2e255 x
               grind)
            | exact superpose b2e255 b2e243
            | exact resolve b2e243 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e243
          have b2e347 : x ≠ y := by
            first
            | (have i₁ := b2e23
               have i₂ := b2e255 y
               grind)
            | exact superpose b2e255 b2e23
            | exact resolve b2e23 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e730 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 X1) X2) ∨ (k X3 X2) = (M.op X3 X2) ∨ (M.op X3 X2) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e43 X0 X1 (M.op (M.op X1 X1) X2)
               have i₂ := b2e64 X2 (M.op X1 X1) X0 X3
               grind)
            | exact superpose b2e64 b2e43
            | (have j1 := b2e64 X2 X1 X2 X3
               grind)
            | exact resolve b2e43 b2e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e43 b2e64
          have b2e776 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op y X2) ∨ (k X3 X2) = (M.op X3 X2) ∨ (M.op X3 X2) = X3 := by
            intro X0 X2 X3
            first
            | (have i₁ := b2e730 X0 x X2 X3
               have i₂ := b2e255 x
               grind)
            | exact superpose b2e255 b2e730
            | (have j0 := b2e730 X0 x X2 X3
               grind)
            | exact resolve b2e730 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e730
          have b2e806 : ∀ X2 X3 : G, (k X3 X2) = (M.op X3 X2) ∨ y = (M.op y X2) ∨ (M.op X3 X2) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b2e776 x X2 X3
               have i₂ := b2e255 x
               grind)
            | exact superpose b2e255 b2e776
            | (have j0 := b2e776 x X2 X3
               grind)
            | exact resolve b2e776 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e776
          have b2e1090 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 X1
               have i₂ := b2e60 X0 X1
               grind)
            | exact superpose b2e60 b2e14
            | (have j1 := b2e60 X0 X1
               grind)
            | exact resolve b2e14 b2e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e60
          have b2e1163 : ∀ X0 X1 : G, (τ y) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e1090 X0 X1
               have i₂ := b2e255 (σ X0)
               grind)
            | exact superpose b2e255 b2e1090
            | (have j0 := b2e1090 X0 X1
               grind)
            | exact resolve b2e1090 b2e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e255 b2e1090
          have b2e1217 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ y = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e1163 X0 X1
               have i₂ := b2e115
               grind)
            | exact superpose b2e115 b2e1163
            | (have j0 := b2e1163 X0 X1
               grind)
            | exact resolve b2e1163 b2e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1163
          have b2e2591 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b2e108 y X0
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e108
            | exact resolve b2e108 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e108
          have b2e6127 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ y = (M.op y X0) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b2e2591 X0
               have i₂ := b2e806 X0 y
               grind)
            | exact superpose b2e806 b2e2591
            | (have j1 := b2e806 X0 y
               grind)
            | exact resolve b2e2591 b2e806
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e806 b2e2591
          have b2e6132 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op y X0)) ∨ y = (M.op y X0) := by
            intro X0
            first
            | (have j0 := b2e6127 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e6127
          have b2e10693 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X0) y)) ∨ y = X1 ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e40 (σ X0) (σ X1)
               have i₂ := b2e1217 X0 X1
               grind)
            | exact superpose b2e1217 b2e40
            | (have j1 := b2e1217 X0 X1
               grind)
            | exact resolve b2e40 b2e1217
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1217
          have b2e237751 : (τ x) = (k y (τ (M.op x (σ y)))) ∨ x = y := by
            first
            | (have i₁ := b2e6132 (M.op x (σ y))
               have i₂ := b2e46
               grind)
            | exact superpose b2e46 b2e6132
            | exact resolve b2e6132 b2e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e46 b2e6132
          have b2e237860 : (τ x) = (k y (τ (M.op x (σ y)))) := by
            first
            | (have r₁ := b2e237751
               have r₂ := b2e347
               grind)
            | exact resolve b2e237751 b2e347
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e347 b2e237751
          have b2e237883 : (τ x) = (k y (τ (M.op x y))) := by
            first
            | (have i₁ := b2e237860
               have i₂ := b2e75
               grind)
            | exact superpose b2e75 b2e237860
            | exact resolve b2e237860 b2e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e75 b2e237860
          have b2e238886 : (σ (τ x)) = (k (σ y) (M.op x y)) := by
            first
            | (have i₁ := b2e30 (M.op x y) y
               have i₂ := b2e237883
               grind)
            | exact superpose b2e237883 b2e30
            | exact resolve b2e30 b2e237883
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30 b2e237883
          have b2e238928 : (k y (M.op x y)) = (σ (τ x)) := by
            first
            | (have i₁ := b2e238886
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e238886
            | exact resolve b2e238886 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238886
          have b2e238945 : x = (k y (M.op x y)) := by
            first
            | (have i₁ := b2e238928
               have i₂ := b2e15 x
               grind)
            | exact superpose b2e15 b2e238928
            | exact resolve b2e238928 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e238928
          have b2e254944 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have i₁ := b2e10693 y (M.op x y)
               have i₂ := b2e238945
               grind)
            | exact superpose b2e238945 b2e10693
            | (have j0 := b2e10693 y (M.op x y)
               grind)
            | exact resolve b2e10693 b2e238945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e10693 b2e238945
          have b2e255001 : (σ (M.op x y)) = (M.op (σ x) (M.op y y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have i₁ := b2e254944
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e254944
            | exact resolve b2e254944 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e254944
          have b2e255031 : (σ (M.op x y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have i₁ := b2e255001
               have i₂ := b2e94 (σ x) y
               grind)
            | exact superpose b2e94 b2e255001
            | exact resolve b2e255001 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e94 b2e255001
          have b2e255037 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
            first
            | (have r₁ := b2e255031
               have r₂ := b2e112
               grind)
            | exact resolve b2e255031 b2e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e112 b2e255031
          have b2e255040 : y = (M.op y (σ (M.op x y))) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e255037
               have i₂ := b2e99
               grind)
            | exact superpose b2e99 b2e255037
            | exact resolve b2e255037 b2e99
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e99 b2e255037
          have b2e255079 : (σ (M.op x y)) = (M.op y (M.op y y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e40 y (σ (M.op x y))
               have i₂ := b2e255040
               grind)
            | exact superpose b2e255040 b2e40
            | exact resolve b2e40 b2e255040
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e40 b2e255040
          have b2e255120 : y = (σ (M.op x y)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e255079
               have i₂ := b2e265 y
               grind)
            | (have i₁ := b2e255079
               have i₂ := b2e265 (M.op y (M.op y y))
               grind)
            | exact superpose b2e265 b2e255079
            | exact resolve b2e255079 b2e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e255079
          have b2e255326 : (M.op x y) = (τ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e255120
               grind)
            | exact superpose b2e255120 b2e14
            | exact resolve b2e14 b2e255120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e255120
          have b2e255393 : y = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b2e255326
               have i₂ := b2e115
               grind)
            | exact superpose b2e115 b2e255326
            | exact resolve b2e255326 b2e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e115 b2e255326
          have b2e255394 : y = (M.op x y) := by grind
          clear b2e255393
          have b2e255458 : x = (M.op y y) := by
            first
            | (have i₁ := b2e265 x
               have i₂ := b2e255394
               grind)
            | exact superpose b2e255394 b2e265
            | exact resolve b2e265 b2e255394
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e265 b2e255394
          have b2e255610 : False := by grind
          exact b2e255610
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e21 : y = (M.op x x) := by grind
          have b3e23 : (σ x) = (M.op (σ x) (σ y)) := by grind
          have b3e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b3e13 x x X0
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e13
            | exact resolve b3e13 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e34 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b3e13 y y X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e41 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b3e33 x
               have i₂ := b3e21
               grind)
            | exact superpose b3e21 b3e33
            | exact resolve b3e33 b3e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e57 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b3e13 (M.op x y) y X0
               have i₂ := b3e41
               grind)
            | exact superpose b3e41 b3e13
            | exact resolve b3e13 b3e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e41
          have b3e58 : y = (M.op x y) := by
            first
            | (have i₁ := b3e57 x
               have i₂ := b3e34 x
               grind)
            | exact superpose b3e34 b3e57
            | exact resolve b3e57 b3e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e34 b3e57
          have b3e82 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e58
               grind)
            | exact superpose b3e58 b3e26
            | exact resolve b3e26 b3e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e84 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b3e13 y x X0
               have i₂ := b3e58
               grind)
            | exact superpose b3e58 b3e13
            | exact resolve b3e13 b3e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e58
          have b3e85 : x = y := by
            first
            | (have i₁ := b3e84 x
               have i₂ := b3e33 x
               grind)
            | exact superpose b3e33 b3e84
            | exact resolve b3e84 b3e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33 b3e84
          have b3e159 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e82
               have i₂ := b3e85
               grind)
            | exact superpose b3e85 b3e82
            | exact resolve b3e82 b3e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e82 b3e85
          have b3e160 : False := by grind
          exact b3e160
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b4e22 : y = (M.op x x) := by grind
            have b4e25 : x ≠ (M.op y y) := by grind
            have b4e26 : y = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e33 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b4e14 x y X0
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e14
              | exact resolve b4e14 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e36 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b4e14 X1 X0 x
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e77 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b4e33 x
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e33
              | exact resolve b4e33 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e81 : x = (M.op y x) := by
              first
              | (have i₁ := b4e33 y
                 have i₂ := b4e77
                 grind)
              | exact superpose b4e77 b4e33
              | exact resolve b4e33 b4e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e33 b4e77
            have b4e86 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b4e36 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                 have i₂ := b4e14 X0 X1 X2
                 grind)
              | exact superpose b4e14 b4e36
              | exact resolve b4e36 b4e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e91 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1
              first
              | (have i₁ := b4e36 (M.op X1 X0) (M.op X1 y)
                 have i₂ := b4e36 X1 X0
                 grind)
              | exact superpose b4e36 b4e36
              | exact resolve b4e36 b4e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e108 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
              intro X1 X2
              first
              | (have i₁ := b4e86 x X1 X2
                 have i₂ := b4e91 x X1
                 grind)
              | exact superpose b4e91 b4e86
              | exact resolve b4e86 b4e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e86 b4e91
            have b4e112 : x = y := by
              first
              | (have i₁ := b4e26
                 have i₂ := b4e81
                 grind)
              | exact superpose b4e81 b4e26
              | exact resolve b4e26 b4e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e113 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b4e36 y x
                 have i₂ := b4e81
                 grind)
              | exact superpose b4e81 b4e36
              | exact resolve b4e36 b4e81
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e36 b4e81
            have b4e117 : x = (M.op x y) := by
              first
              | (have i₁ := b4e113
                 have i₂ := b4e108 x y
                 grind)
              | exact superpose b4e108 b4e113
              | exact resolve b4e113 b4e108
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e108 b4e113
            have b4e119 : x = (M.op x x) := by
              first
              | (have i₁ := b4e117
                 have i₂ := b4e112
                 grind)
              | exact superpose b4e112 b4e117
              | exact resolve b4e117 b4e112
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e117
            have b4e130 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e112
                 grind)
              | exact superpose b4e112 b4e25
              | exact resolve b4e25 b4e112
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e112
            have b4e146 : False := by grind
            exact b4e146
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e22 : y = (M.op x x) := by grind
            have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b5e20 (τ X0) X1
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e20
              | exact resolve b5e20 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e35 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 X0 x
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e37 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b5e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e75 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 (M.op y X0) y
                 have i₂ := b5e35 y X0
                 grind)
              | exact superpose b5e35 b5e14
              | exact resolve b5e14 b5e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e94 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b5e75 X0 (M.op y y)
                 have i₂ := b5e35 y X0
                 grind)
              | exact superpose b5e35 b5e75
              | exact resolve b5e75 b5e35
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e121 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
              intro X0
              grind
            have b5e127 : y = (M.op y y) := by
              first
              | (have i₁ := b5e35 x y
                 have i₂ := b5e94 (M.op x y)
                 grind)
              | exact superpose b5e94 b5e35
              | exact resolve b5e35 b5e94
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e35 b5e94
            have b5e145 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b5e121 X0
                 have i₂ := b5e127
                 grind)
              | exact superpose b5e127 b5e121
              | exact resolve b5e121 b5e127
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e121 b5e127
            have b5e164 : ∀ X0 : G, (M.op X0 X0) = y := by
              intro X0
              first
              | (have i₁ := b5e37 X0 y y
                 have i₂ := b5e75 y X0
                 grind)
              | exact superpose b5e75 b5e37
              | exact resolve b5e37 b5e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37 b5e75
            have b5e208 : y ≠ (σ y) := by
              first
              | (have i₁ := b5e23
                 have i₂ := b5e164 (σ x)
                 grind)
              | exact superpose b5e164 b5e23
              | exact resolve b5e23 b5e164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e513 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
              intro X0
              first
              | (have i₁ := b5e30 X0 y
                 have i₂ := b5e145 (τ X0)
                 grind)
              | exact superpose b5e145 b5e30
              | exact resolve b5e30 b5e145
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e30 b5e145
            have b5e517 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e513 X0
                 have i₂ := b5e16 X0
                 grind)
              | exact superpose b5e16 b5e513
              | exact resolve b5e513 b5e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e513
            have b5e848 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e19 X0 (σ y)
                 have i₂ := b5e517 X0
                 grind)
              | exact superpose b5e517 b5e19
              | (have j0 := b5e19 X0 (σ y)
                 grind)
              | exact resolve b5e19 b5e517
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e517
            have b5e851 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) := by
              intro X0
              first
              | (have j0 := b5e848 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e848
            have b5e857 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have i₁ := b5e851 X0
                 have i₂ := b5e164 X0
                 grind)
              | exact superpose b5e164 b5e851
              | (have j0 := b5e851 X0
                 grind)
              | exact resolve b5e851 b5e164
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e851
            have b5e859 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
              intro X0
              first
              | (have j0 := b5e857 X0
                 grind)
              | (have r₁ := b5e857 X0
                 have r₂ := b5e208
                 grind)
              | exact resolve b5e857 b5e208
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e857
            have b5e1096 : y = (σ y) := by
              first
              | (have i₁ := b5e164 (σ y)
                 have i₂ := b5e859 (σ y)
                 grind)
              | exact superpose b5e859 b5e164
              | exact resolve b5e164 b5e859
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e164 b5e859
            have b5e1118 : False := by grind
            exact b5e1118
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b6e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
          have b6e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b6e30 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e13 x x X0
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e31 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e13 y y X0
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e38 : x = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b6e30 x
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e30
            | exact resolve b6e30 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e41 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (M.op x (M.op X0 X0)) y X1
               have i₂ := b6e30 X0
               grind)
            | exact superpose b6e30 b6e13
            | exact resolve b6e13 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e42 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b6e41 X0 x
               have i₂ := b6e31 x
               grind)
            | exact superpose b6e31 b6e41
            | exact resolve b6e41 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e41
          have b6e51 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e13 (M.op x y) y X0
               have i₂ := b6e38
               grind)
            | exact superpose b6e38 b6e13
            | exact resolve b6e13 b6e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e38
          have b6e52 : y = (M.op x y) := by
            first
            | (have i₁ := b6e51 x
               have i₂ := b6e31 x
               grind)
            | exact superpose b6e31 b6e51
            | exact resolve b6e51 b6e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e31 b6e51
          have b6e77 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b6e13 y x X0
               have i₂ := b6e52
               grind)
            | exact superpose b6e52 b6e13
            | exact resolve b6e13 b6e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e52
          have b6e78 : x = y := by
            first
            | (have i₁ := b6e77 x
               have i₂ := b6e30 x
               grind)
            | exact superpose b6e30 b6e77
            | exact resolve b6e77 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e77
          have b6e225 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op x (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b6e13 (M.op X0 X0) x X1
               have i₂ := b6e42 X0
               grind)
            | exact superpose b6e42 b6e13
            | exact resolve b6e13 b6e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e42
          have b6e226 : ∀ X0 : G, (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b6e225 X0 x
               have i₂ := b6e30 x
               grind)
            | exact superpose b6e30 b6e225
            | exact resolve b6e225 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e225
          have b6e253 : ∀ X0 : G, (k X0 x) = X0 := by
            intro X0
            grind
          have b6e266 : x ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e226 (σ x)
               grind)
            | exact superpose b6e226 b6e22
            | exact resolve b6e22 b6e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e268 : x ≠ (σ x) := by
            first
            | (have i₁ := b6e266
               have i₂ := b6e78
               grind)
            | exact superpose b6e78 b6e266
            | exact resolve b6e266 b6e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e266
          have b6e576 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ x)) := by
            intro X0
            first
            | (have i₁ := b6e28 X0 x
               have i₂ := b6e253 (τ X0)
               grind)
            | exact superpose b6e253 b6e28
            | exact resolve b6e28 b6e253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e28 b6e253
          have b6e579 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e576 X0
               have i₂ := b6e15 X0
               grind)
            | exact superpose b6e15 b6e576
            | exact resolve b6e576 b6e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e576
          have b6e620 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 X0) = (σ x) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e18 X0 (σ x)
               have i₂ := b6e579 X0
               grind)
            | exact superpose b6e579 b6e18
            | (have j0 := b6e18 X0 (σ x)
               grind)
            | exact resolve b6e18 b6e579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e579
          have b6e623 : ∀ X0 : G, (M.op X0 (σ x)) = X0 ∨ (M.op X0 X0) = (σ x) := by
            intro X0
            first
            | (have j0 := b6e620 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e620
          have b6e626 : ∀ X0 : G, x = (σ x) ∨ (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have i₁ := b6e623 X0
               have i₂ := b6e226 X0
               grind)
            | exact superpose b6e226 b6e623
            | (have j0 := b6e623 X0
               grind)
            | exact resolve b6e623 b6e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e226 b6e623
          have b6e628 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
            intro X0
            first
            | (have j0 := b6e626 X0
               grind)
            | (have r₁ := b6e626 X0
               have r₂ := b6e268
               grind)
            | exact resolve b6e626 b6e268
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e268 b6e626
          have b6e671 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b6e22
               have i₂ := b6e628 (σ x)
               grind)
            | exact superpose b6e628 b6e22
            | exact resolve b6e22 b6e628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e628
          have b6e673 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e671
               have i₂ := b6e78
               grind)
            | exact superpose b6e78 b6e671
            | exact resolve b6e671 b6e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e78 b6e671
          have b6e674 : False := by grind
          exact b6e674
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : y = (M.op x x) := by grind
            have b7e25 : x ≠ (M.op y y) := by grind
            have b7e26 : y = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e32 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b7e14 x y X0
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e14
              | exact resolve b7e14 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e34 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 X0 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e69 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b7e32 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e32
              | exact resolve b7e32 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e75 : x = (M.op y x) := by
              first
              | (have i₁ := b7e32 y
                 have i₂ := b7e69
                 grind)
              | exact superpose b7e69 b7e32
              | exact resolve b7e32 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e32 b7e69
            have b7e81 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e34 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                 have i₂ := b7e14 X0 X1 X2
                 grind)
              | exact superpose b7e14 b7e34
              | exact resolve b7e34 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e86 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 X0) y)) = (M.op X1 y) := by
              intro X0 X1
              first
              | (have i₁ := b7e34 (M.op X1 X0) (M.op X1 y)
                 have i₂ := b7e34 X1 X0
                 grind)
              | exact superpose b7e34 b7e34
              | exact resolve b7e34 b7e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e101 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
              intro X1 X2
              first
              | (have i₁ := b7e81 x X1 X2
                 have i₂ := b7e86 x X1
                 grind)
              | exact superpose b7e86 b7e81
              | exact resolve b7e81 b7e86
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e81 b7e86
            have b7e105 : x = y := by
              first
              | (have i₁ := b7e26
                 have i₂ := b7e75
                 grind)
              | exact superpose b7e75 b7e26
              | exact resolve b7e26 b7e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e106 : x = (M.op x (M.op y y)) := by
              first
              | (have i₁ := b7e34 y x
                 have i₂ := b7e75
                 grind)
              | exact superpose b7e75 b7e34
              | exact resolve b7e34 b7e75
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e34 b7e75
            have b7e110 : x = (M.op x y) := by
              first
              | (have i₁ := b7e106
                 have i₂ := b7e101 x y
                 grind)
              | exact superpose b7e101 b7e106
              | exact resolve b7e106 b7e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e101 b7e106
            have b7e112 : x = (M.op x x) := by
              first
              | (have i₁ := b7e110
                 have i₂ := b7e105
                 grind)
              | exact superpose b7e105 b7e110
              | exact resolve b7e110 b7e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e110
            have b7e124 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e105
                 grind)
              | exact superpose b7e105 b7e25
              | exact resolve b7e25 b7e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e105
            have b7e138 : False := by grind
            exact b7e138
          · have b8e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
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
            have b8e22 : y = (M.op x x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 X0 x
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e14
              | exact resolve b8e14 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b8e23
                 have i₂ := b8e19 (σ x) X0
                 grind)
              | (have i₁ := b8e23
                 have i₂ := b8e19 X0 (M.op (σ x) (σ x))
                 grind)
              | exact superpose b8e19 b8e23
              | (have j1 := b8e19 (σ x) X0
                 grind)
              | (have r₁ := b8e23
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e23 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e68 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b8e14 X1 (M.op y X0) y
                 have i₂ := b8e33 y X0
                 grind)
              | exact superpose b8e33 b8e14
              | exact resolve b8e14 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e87 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b8e68 X0 (M.op y y)
                 have i₂ := b8e33 y X0
                 grind)
              | exact superpose b8e33 b8e68
              | exact resolve b8e68 b8e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e68
            have b8e114 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
              intro X0
              grind
            have b8e120 : y = (M.op y y) := by
              first
              | (have i₁ := b8e33 x y
                 have i₂ := b8e87 (M.op x y)
                 grind)
              | exact superpose b8e87 b8e33
              | exact resolve b8e33 b8e87
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e33 b8e87
            have b8e138 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b8e114 X0
                 have i₂ := b8e120
                 grind)
              | exact superpose b8e120 b8e114
              | exact resolve b8e114 b8e120
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e114 b8e120
            have b8e459 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have j0 := b8e58 (σ y)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e58
            have b8e460 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e459
                 have r₂ := b8e24
                 grind)
              | exact resolve b8e459 b8e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e459
            have b8e461 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e460
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e460
              | exact resolve b8e460 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e460
            have b8e462 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b8e461
                 have i₂ := b8e138 x
                 grind)
              | exact superpose b8e138 b8e461
              | exact resolve b8e461 b8e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e138 b8e461
            have b8e463 : False := by grind
            exact b8e463
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b9e22 : x = (M.op x y) := by grind
          have b9e23 : (σ y) = (M.op (σ x) (σ x)) := by grind
          have b9e24 : x = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b9e20
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e20
            | exact resolve b9e20 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e44 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b9e13 y x X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e53 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b9e44 y
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e44
            | exact resolve b9e44 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e63 : y = (M.op x y) := by
            first
            | (have i₁ := b9e44 x
               have i₂ := b9e53
               grind)
            | exact superpose b9e53 b9e44
            | exact resolve b9e44 b9e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e44 b9e53
          have b9e66 : x = y := by
            first
            | (have i₁ := b9e63
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e63
            | exact resolve b9e63 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e63
          have b9e95 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b9e26
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e26
            | exact resolve b9e26 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e26
          have b9e99 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b9e95
               have i₂ := b9e23
               grind)
            | exact superpose b9e23 b9e95
            | exact resolve b9e95 b9e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e95
          have b9e100 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b9e99
               have i₂ := b9e66
               grind)
            | exact superpose b9e66 b9e99
            | exact resolve b9e99 b9e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e66 b9e99
          have b9e101 : False := by grind
          exact b9e101
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e22 : y ≠ (M.op x x) := by grind
            have b10e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            have b10e25 : x ≠ (M.op y y) := by grind
            have b10e26 : y = (M.op y x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e48 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b10e14 x y X0
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e14
              | exact resolve b10e14 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e51 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b10e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b10e14 b10e14
              | exact resolve b10e14 b10e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e79 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b10e14 X1 X1 X2
                 have i₂ := b10e19 X1 X0
                 grind)
              | (have i₁ := b10e14 X0 X1 X2
                 have i₂ := b10e19 X0 (M.op X1 X0)
                 grind)
              | exact superpose b10e19 b10e14
              | (have j1 := b10e19 X1 X0
                 grind)
              | exact resolve b10e14 b10e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e138 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b10e51 X0 (M.op X1 X1) (M.op X1 X1)
                 have i₂ := b10e51 (M.op X1 X1) X1 X0
                 grind)
              | exact superpose b10e51 b10e51
              | exact resolve b10e51 b10e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e51
            have b10e182 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              grind
            have b10e195 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
              intro X0
              first
              | (have i₁ := b10e24
                 have i₂ := b10e138 (σ x) X0
                 grind)
              | (have i₁ := b10e24
                 have i₂ := b10e138 X0 (σ x)
                 grind)
              | exact superpose b10e138 b10e24
              | exact resolve b10e24 b10e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e196 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
              intro X0
              first
              | (have i₁ := b10e22
                 have i₂ := b10e138 x X0
                 grind)
              | (have i₁ := b10e22
                 have i₂ := b10e138 X0 x
                 grind)
              | exact superpose b10e138 b10e22
              | exact resolve b10e22 b10e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e197 : ∀ X0 : G, (M.op X0 X0) ≠ x := by
              intro X0
              first
              | (have i₁ := b10e25
                 have i₂ := b10e138 y X0
                 grind)
              | (have i₁ := b10e25
                 have i₂ := b10e138 X0 y
                 grind)
              | exact superpose b10e138 b10e25
              | exact resolve b10e25 b10e138
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e138
            have b10e204 : ∀ X1 : G, (k X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b10e182 x X1
                 have i₂ := b10e195 x
                 grind)
              | exact superpose b10e195 b10e182
              | exact resolve b10e182 b10e195
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e182
            have b10e238 : y ≠ (σ y) := by
              first
              | (have i₁ := b10e196 (σ x)
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e196
              | exact resolve b10e196 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e465 : ∀ X0 X1 : G, x ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b10e197 X1
                 have i₂ := b10e19 X1 X0
                 grind)
              | (have i₁ := b10e197 X0
                 have i₂ := b10e19 X0 (M.op X0 X0)
                 grind)
              | exact superpose b10e19 b10e197
              | (have j1 := b10e19 X1 X0
                 grind)
              | (have r₁ := b10e197 X0
                 have r₂ := b10e19 X0 x
                 grind)
              | (have r₁ := b10e197 x
                 have r₂ := b10e19 x x
                 grind)
              | exact resolve b10e197 b10e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e197
            have b10e665 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
              intro X0
              first
              | (have i₁ := b10e20 X0 y
                 have i₂ := b10e204 (σ X0)
                 grind)
              | exact superpose b10e204 b10e20
              | exact resolve b10e20 b10e204
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e204
            have b10e740 : x = y ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b10e48 x
                 have i₂ := b10e79 y y x
                 grind)
              | exact superpose b10e79 b10e48
              | (have j1 := b10e79 y y x
                 grind)
              | exact resolve b10e48 b10e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e48 b10e79
            have b10e741 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
              first
              | (have j1 := b10e465 y y
                 grind)
              | (have r₁ := b10e740
                 have r₂ := b10e465 y x
                 grind)
              | exact resolve b10e740 b10e465
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e465 b10e740
            have b10e792 : (M.op y y) = (k y y) := by
              first
              | (have r₁ := b10e741
                 have r₂ := b10e196 y
                 grind)
              | exact resolve b10e741 b10e196
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e196 b10e741
            have b10e835 : (σ y) = (k y y) := by
              first
              | (have i₁ := b10e792
                 have i₂ := b10e195 y
                 grind)
              | exact superpose b10e195 b10e792
              | exact resolve b10e792 b10e195
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e195 b10e792
            have b10e1171 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
              intro X0
              first
              | (have i₁ := b10e15 (k X0 y)
                 have i₂ := b10e665 X0
                 grind)
              | exact superpose b10e665 b10e15
              | exact resolve b10e15 b10e665
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e665
            have b10e1184 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b10e1171 X0
                 have i₂ := b10e15 X0
                 grind)
              | exact superpose b10e15 b10e1171
              | exact resolve b10e1171 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e1171
            have b10e1422 : y = (σ y) := by
              first
              | (have i₁ := b10e835
                 have i₂ := b10e1184 y
                 grind)
              | exact superpose b10e1184 b10e835
              | exact resolve b10e835 b10e1184
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e835 b10e1184
            have b10e1434 : False := by grind
            exact b10e1434
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e22 : y ≠ (M.op x x) := by grind
            have b11e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e33 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 (τ X0) X1
                 have i₂ := b11e16 X0
                 grind)
              | exact superpose b11e16 b11e20
              | exact resolve b11e20 b11e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e43 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b11e15 (k (τ X0) X1)
                 have i₂ := b11e33 X0 X1
                 grind)
              | exact superpose b11e33 b11e15
              | exact resolve b11e15 b11e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e33
            have b11e50 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b11e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e129 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
              intro X0 X1
              first
              | (have i₁ := b11e50 X0 (M.op X1 X1) (M.op X1 X1)
                 have i₂ := b11e50 (M.op X1 X1) X1 X0
                 grind)
              | exact superpose b11e50 b11e50
              | exact resolve b11e50 b11e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e50
            have b11e172 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              grind
            have b11e184 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
              intro X0
              first
              | (have i₁ := b11e24
                 have i₂ := b11e129 (σ x) X0
                 grind)
              | (have i₁ := b11e24
                 have i₂ := b11e129 X0 (σ x)
                 grind)
              | exact superpose b11e129 b11e24
              | exact resolve b11e24 b11e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e185 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
              intro X0
              first
              | (have i₁ := b11e22
                 have i₂ := b11e129 x X0
                 grind)
              | (have i₁ := b11e22
                 have i₂ := b11e129 X0 x
                 grind)
              | exact superpose b11e129 b11e22
              | exact resolve b11e22 b11e129
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e129
            have b11e193 : ∀ X1 : G, (k X1 (σ y)) = X1 := by
              intro X1
              first
              | (have i₁ := b11e172 x X1
                 have i₂ := b11e184 x
                 grind)
              | exact superpose b11e184 b11e172
              | exact resolve b11e172 b11e184
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e172 b11e184
            have b11e627 : ∀ X0 : G, (τ X0) = (k (τ X0) y) := by
              intro X0
              first
              | (have i₁ := b11e43 X0 y
                 have i₂ := b11e193 X0
                 grind)
              | exact superpose b11e193 b11e43
              | exact resolve b11e43 b11e193
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e43 b11e193
            have b11e1043 : ∀ X0 : G, (k X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e627 (σ X0)
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e627
              | exact resolve b11e627 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e627
            have b11e1126 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y ∨ (M.op X0 y) = X0 := by
              intro X0
              first
              | (have i₁ := b11e19 X0 y
                 have i₂ := b11e1043 X0
                 grind)
              | exact superpose b11e1043 b11e19
              | (have j0 := b11e19 X0 y
                 grind)
              | exact resolve b11e19 b11e1043
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1043
            have b11e1130 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y := by
              intro X0
              first
              | (have j0 := b11e1126 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1126
            have b11e1142 : ∀ X0 : G, (M.op X0 y) = X0 := by
              intro X0
              first
              | (have j0 := b11e1130 X0
                 grind)
              | (have r₁ := b11e1130 y
                 have r₂ := b11e185 y
                 grind)
              | (have r₁ := b11e1130 X0
                 have r₂ := b11e185 X0
                 grind)
              | exact resolve b11e1130 b11e185
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1130
            have b11e1377 : y ≠ y := by
              first
              | (have i₁ := b11e185 y
                 have i₂ := b11e1142 y
                 grind)
              | exact superpose b11e1142 b11e185
              | (have r₁ := b11e185 y
                 have r₂ := b11e1142 y
                 grind)
              | exact resolve b11e185 b11e1142
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e185 b11e1142
            have b11e1392 : False := by grind
            exact b11e1392
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b12e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b12e23 : x = (M.op x y) := by grind
            have b12e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e28 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b12e21
                 have i₂ := b12e25
                 grind)
              | exact superpose b12e25 b12e21
              | exact resolve b12e21 b12e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e29 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b12e28
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e28
              | exact resolve b12e28 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e28
            have b12e30 : False := by grind
            exact b12e30
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = (M.op x y) := by grind
              have b13e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e30 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b13e22
                   have i₂ := b13e26
                   grind)
                | exact superpose b13e26 b13e22
                | exact resolve b13e22 b13e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e31 : (σ x) ≠ (σ x) := by
                first
                | (have i₁ := b13e30
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e30
                | exact resolve b13e30 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e30
              have b13e32 : False := by grind
              exact b13e32
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
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e22 : y ≠ (M.op x x) := by grind
            have b15e23 : x = (M.op x y) := by grind
            have b15e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e38 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b15e14 y x X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e45 : y = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b15e38 y
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e38
              | exact resolve b15e38 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e75 : y = (M.op x y) := by
              first
              | (have i₁ := b15e38 x
                 have i₂ := b15e45
                 grind)
              | exact superpose b15e45 b15e38
              | exact resolve b15e38 b15e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e38 b15e45
            have b15e78 : x = y := by
              first
              | (have i₁ := b15e75
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e75
              | exact resolve b15e75 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e75
            have b15e92 : x = (M.op x x) := by
              first
              | (have i₁ := b15e26
                 have i₂ := b15e78
                 grind)
              | exact superpose b15e78 b15e26
              | exact resolve b15e26 b15e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e124 : x ≠ y := by
              first
              | (have i₁ := b15e22
                 have i₂ := b15e92
                 grind)
              | exact superpose b15e92 b15e22
              | exact resolve b15e22 b15e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e92
            have b15e134 : False := by grind
            exact b15e134
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b16e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b16e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b16e23 : y ≠ (M.op x x) := by grind
              have b16e24 : x = (M.op x y) := by grind
              have b16e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b16e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e47 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
                first
                | (have i₁ := b16e19 x y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e19
                | (have j0 := b16e19 x y
                   grind)
                | (have r₁ := b16e19 x y
                   have r₂ := b16e24
                   grind)
                | exact resolve b16e19 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e52 : y = (M.op x x) ∨ x = (k x y) := by grind
              clear b16e47
              have b16e54 : x = (k x y) := by
                first
                | (have r₁ := b16e52
                   have r₂ := b16e23
                   grind)
                | exact resolve b16e52 b16e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e52
              have b16e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b16e25
                   have i₂ := b16e20 (σ x) X0
                   grind)
                | (have i₁ := b16e25
                   have i₂ := b16e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b16e20 b16e25
                | (have j1 := b16e20 (σ x) X0
                   grind)
                | (have r₁ := b16e25
                   have r₂ := b16e20 (σ x) (σ y)
                   grind)
                | exact resolve b16e25 b16e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e261 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b16e69 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e69
              have b16e262 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b16e261
                   have r₂ := b16e26
                   grind)
                | exact resolve b16e261 b16e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e261
              have b16e263 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b16e262
                   have i₂ := b16e21 x y
                   grind)
                | exact superpose b16e21 b16e262
                | exact resolve b16e262 b16e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e262
              have b16e264 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b16e263
                   have i₂ := b16e54
                   grind)
                | exact superpose b16e54 b16e263
                | exact resolve b16e263 b16e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e54 b16e263
              have b16e265 : False := by grind
              exact b16e265
            · have b17e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e46 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
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
              have b17e49 : y = (M.op x x) ∨ x = (k x y) := by grind
              clear b17e46
              have b17e50 : x = (k x y) := by
                first
                | (have r₁ := b17e49
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e49 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e49
              have b17e65 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
                intro X0
                first
                | (have i₁ := b17e25
                   have i₂ := b17e20 (σ x) X0
                   grind)
                | (have i₁ := b17e25
                   have i₂ := b17e20 X0 (M.op (σ x) (σ x))
                   grind)
                | exact superpose b17e20 b17e25
                | (have j1 := b17e20 (σ x) X0
                   grind)
                | (have r₁ := b17e25
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e25 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have j0 := b17e65 (σ y)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e65
              have b17e240 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e239
                   have r₂ := b17e26
                   grind)
                | exact resolve b17e239 b17e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e239
              have b17e241 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e240
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e240
                | exact resolve b17e240 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e240
              have b17e242 : (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b17e241
                   have i₂ := b17e50
                   grind)
                | exact superpose b17e50 b17e241
                | exact resolve b17e241 b17e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e50 b17e241
              have b17e243 : False := by grind
              exact b17e243
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
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
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e27 : (σ x) = (k (σ x) (σ y)) := by grind
          have b18e28 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e27
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e27
            | exact resolve b18e27 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e27
          have b18e29 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e28
               grind)
            | exact superpose b18e28 b18e14
            | exact resolve b18e14 b18e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e28
          have b18e30 : x = (k x y) := by
            first
            | (have i₁ := b18e29
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e29
            | exact resolve b18e29 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e69 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b18e30
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e30
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e30 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e30
          have b18e81 : x = (M.op x y) ∨ y = (M.op x x) := by grind
          clear b18e69
          have b18e85 : y = (M.op x x) := by
            first
            | (have r₁ := b18e81
               have r₂ := b18e22
               grind)
            | exact resolve b18e81 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e81
          have b18e88 : False := by grind
          exact b18e88
        · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op x x) := by grind
            have b19e23 : x ≠ (M.op x y) := by grind
            have b19e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e28 : (σ x) = (k (σ x) (σ y)) := by grind
            have b19e29 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e28
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e28
              | exact resolve b19e28 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e28
            have b19e30 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e29
                 grind)
              | exact superpose b19e29 b19e15
              | exact resolve b19e15 b19e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29
            have b19e31 : x = (k x y) := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e30
              | exact resolve b19e30 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e68 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b19e31
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e31
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e31 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31
            have b19e80 : x = (M.op x y) ∨ y = (M.op x x) := by grind
            clear b19e68
            have b19e84 : y = (M.op x x) := by
              first
              | (have r₁ := b19e80
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e80 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e80
            have b19e87 : False := by grind
            exact b19e87
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
            have b20e78 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
            have b20e90 : x = (M.op x y) ∨ y = (M.op x x) := by grind
            clear b20e78
            have b20e95 : y = (M.op x x) := by
              first
              | (have r₁ := b20e90
                 have r₂ := b20e23
                 grind)
              | exact resolve b20e90 b20e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e90
            have b20e100 : False := by grind
            exact b20e100
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b21e18 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b21e22 : y ≠ (M.op x x) := by grind
            have b21e23 : x ≠ (M.op x y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ x) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e28 : (σ (M.op x y)) ≠ (σ x) := by
              first
              | (have i₁ := b21e21
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e21
              | exact resolve b21e21 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
            have b21e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
            clear b21e43
            have b21e47 : (σ x) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e46
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e46 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e46
            have b21e48 : (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b21e47
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e47
              | exact resolve b21e47 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e47
            have b21e60 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have i₁ := b21e48
                 have i₂ := b21e19 x y
                 grind)
              | exact superpose b21e19 b21e48
              | (have j1 := b21e19 x y
                 grind)
              | exact resolve b21e48 b21e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e48
            have b21e72 : y = (M.op x x) ∨ x = (M.op x y) := by
              first
              | (have r₁ := b21e60
                 have r₂ := b21e28
                 grind)
              | exact resolve b21e60 b21e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e28 b21e60
            have b21e73 : x = (M.op x y) := by
              first
              | (have r₁ := b21e72
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e72 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e72
            have b21e74 : False := by grind
            exact b21e74
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b22e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b22e23 : y ≠ (M.op x x) := by grind
              have b22e24 : x ≠ (M.op x y) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b22e26 : (σ x) = (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e30 : (σ (M.op x y)) ≠ (σ x) := by
                first
                | (have i₁ := b22e22
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e22
                | exact resolve b22e22 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e43 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
                first
                | (have i₁ := b22e19 (σ x) (σ y)
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e19
                | (have j0 := b22e19 (σ x) (σ y)
                   grind)
                | (have r₁ := b22e19 (σ x) (σ y)
                   have r₂ := b22e26
                   grind)
                | exact resolve b22e19 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e45 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b22e43
              have b22e47 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e45
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e45 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e45
              have b22e49 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e47
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e47
                | exact resolve b22e47 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e47
              have b22e66 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b22e49
                   have i₂ := b22e20 x y
                   grind)
                | exact superpose b22e20 b22e49
                | (have j1 := b22e20 x y
                   grind)
                | exact resolve b22e49 b22e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e49
              have b22e73 : y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b22e66
                   have r₂ := b22e30
                   grind)
                | exact resolve b22e66 b22e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e30 b22e66
              have b22e74 : x = (M.op x y) := by
                first
                | (have r₁ := b22e73
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e73 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e73
              have b22e75 : False := by grind
              exact b22e75
            · have b23e19 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
              have b23e44 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
              have b23e46 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
              clear b23e44
              have b23e47 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e46
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e46 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e46
              have b23e48 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b23e47
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e47
                | exact resolve b23e47 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e47
              have b23e60 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b23e48
                   have i₂ := b23e20 x y
                   grind)
                | exact superpose b23e20 b23e48
                | (have j1 := b23e20 x y
                   grind)
                | exact resolve b23e48 b23e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e48
              have b23e68 : y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have r₁ := b23e60
                   have r₂ := b23e30
                   grind)
                | exact resolve b23e60 b23e30
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e30 b23e60
              have b23e69 : x = (M.op x y) := by
                first
                | (have r₁ := b23e68
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e68 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e68
              have b23e70 : False := by grind
              exact b23e70
        · rcases eq_or_ne (M.op y y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
            have b24e26 : x = (M.op y y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e31 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b24e14 y y X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 X0 y
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e35 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b24e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
            have b24e55 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X1 X1 X2
                 have i₂ := b24e19 X1 X0
                 grind)
              | (have i₁ := b24e14 X0 X1 X2
                 have i₂ := b24e19 X0 (M.op X1 X0)
                 grind)
              | exact superpose b24e19 b24e14
              | (have j1 := b24e19 X1 X0
                 grind)
              | exact resolve b24e14 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e62 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) x)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e33 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e33
              | exact resolve b24e33 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e63 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) x)) := by
              intro X0 X1
              first
              | (have i₁ := b24e33 (M.op X1 X0) (M.op X1 x)
                 have i₂ := b24e33 X1 X0
                 grind)
              | exact superpose b24e33 b24e33
              | exact resolve b24e33 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e68 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e14 X1 (M.op x X0) x
                 have i₂ := b24e33 x X0
                 grind)
              | exact superpose b24e33 b24e14
              | exact resolve b24e14 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e76 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
              intro X1 X2
              first
              | (have i₁ := b24e62 x X1 X2
                 have i₂ := b24e63 x X1
                 grind)
              | exact superpose b24e63 b24e62
              | exact resolve b24e62 b24e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e62 b24e63
            have b24e160 : ∀ X0 : G, (M.op X0 X0) = x := by
              intro X0
              first
              | (have i₁ := b24e35 X0 x x
                 have i₂ := b24e68 x X0
                 grind)
              | exact superpose b24e68 b24e35
              | exact resolve b24e35 b24e68
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e35 b24e68
            have b24e654 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b24e31 (M.op X0 X0)
                 have i₂ := b24e55 y (M.op X0 X0) X0
                 grind)
              | exact superpose b24e55 b24e31
              | (have j1 := b24e55 y (M.op X0 X0) x
                 grind)
              | exact resolve b24e31 b24e55
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31 b24e55
            have b24e655 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b24e654 X0
                 have i₂ := b24e76 x X0
                 grind)
              | exact superpose b24e76 b24e654
              | (have j0 := b24e654 X0
                 grind)
              | exact resolve b24e654 b24e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e76 b24e654
            have b24e698 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k (M.op X0 X0) y) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have j0 := b24e655 X0
                 grind)
              | (have r₁ := b24e655 X0
                 have r₂ := b24e22
                 grind)
              | exact resolve b24e655 b24e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e655
            have b24e732 : ∀ X0 : G, (M.op x y) = (k x y) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b24e698 X0
                 have i₂ := b24e160 X0
                 grind)
              | exact superpose b24e160 b24e698
              | (have j0 := b24e698 X0
                 grind)
              | exact resolve b24e698 b24e160
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e698
            have b24e752 : x = (M.op x y) ∨ (M.op x y) = (k x y) := by
              first
              | (have i₁ := b24e732 x
                 have i₂ := b24e160 x
                 grind)
              | exact superpose b24e160 b24e732
              | exact resolve b24e732 b24e160
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e160 b24e732
            have b24e763 : (M.op x y) = (k x y) := by
              first
              | (have r₁ := b24e752
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e752 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e752
            have b24e815 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e50 x y
                 grind)
              | exact superpose b24e50 b24e21
              | (have j1 := b24e50 x y
                 grind)
              | exact resolve b24e21 b24e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e50
            have b24e915 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b24e815
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e815 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e815
            have b24e962 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have r₁ := b24e915
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e915 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e915
            have b24e990 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
              first
              | (have i₁ := b24e962
                 have i₂ := b24e763
                 grind)
              | exact superpose b24e763 b24e962
              | exact resolve b24e962 b24e763
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e763 b24e962
            have b24e991 : False := by grind
            exact b24e991
          · rcases eq_or_ne (M.op y x) (y) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op x x) := by grind
              have b25e24 : x ≠ (M.op x y) := by grind
              have b25e25 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              have b25e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X0 X1
                   have i₂ := b25e20 (σ X0) (σ X1)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X0) (σ X1)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e446 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e48 x y
                   grind)
                | exact superpose b25e48 b25e22
                | (have j1 := b25e48 x y
                   grind)
                | exact resolve b25e22 b25e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e48
              have b25e530 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b25e446
                   have r₂ := b25e25
                   grind)
                | exact resolve b25e446 b25e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e446
              have b25e538 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b25e530
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e530 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e530
              have b25e541 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e538
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e538
                | (have j1 := b25e20 x y
                   grind)
                | exact resolve b25e538 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e538
              have b25e542 : y = (M.op x x) ∨ x = (M.op x y) := by grind
              clear b25e541
              have b25e544 : x = (M.op x y) := by
                first
                | (have r₁ := b25e542
                   have r₂ := b25e23
                   grind)
                | exact resolve b25e542 b25e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e542
              have b25e546 : False := by grind
              exact b25e546
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
              have b26e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
              have b26e434 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e55 x y
                   grind)
                | exact superpose b26e55 b26e22
                | (have j1 := b26e55 x y
                   grind)
                | exact resolve b26e22 b26e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e55
              have b26e520 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
                first
                | (have r₁ := b26e434
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e434 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e434
              have b26e528 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have r₁ := b26e520
                   have r₂ := b26e26
                   grind)
                | exact resolve b26e520 b26e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e520
              have b26e531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b26e528
                   have i₂ := b26e20 x y
                   grind)
                | exact superpose b26e20 b26e528
                | (have j1 := b26e20 x y
                   grind)
                | exact resolve b26e528 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e528
              have b26e532 : y = (M.op x x) ∨ x = (M.op x y) := by grind
              clear b26e531
              have b26e534 : x = (M.op x y) := by
                first
                | (have r₁ := b26e532
                   have r₂ := b26e23
                   grind)
                | exact resolve b26e532 b26e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e532
              have b26e536 : False := by grind
              exact b26e536

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then Y else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_y_y_pxy_Equation1496 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x y) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e22
        | exact resolve b0e22 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e24 : False := by grind
      exact b0e24
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e29 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k (τ X0) X1)
             have i₂ := b1e29 X0 X1
             grind)
          | exact superpose b1e29 b1e13
          | exact resolve b1e13 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e35 : ∀ X0 : G, y = (M.op y (M.op x (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b1e12 y x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (σ x))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
             have i₂ := b1e12 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) ≠ X0 ∨ (M.op X1 (M.op X2 X2)) = (k (M.op X1 X0) (M.op X1 (M.op X2 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e15 (M.op X1 X0) (M.op X1 (M.op X2 X2))
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 (M.op X1 X0) (M.op X1 (M.op X2 X2))
             grind)
          | (have r₁ := b1e15 (M.op X1 (M.op X1 (M.op X2 X2))) (M.op X1 (M.op X2 X2))
             have r₂ := b1e12 (M.op X1 (M.op X2 X2)) X1 X2
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : y = (M.op y (M.op x (σ x))) := by
          first
          | (have i₁ := b1e35 (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e35
          | exact resolve b1e35 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e61 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X1 X2
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e17 (M.op X1 X0) X1
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X0 X1
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e85 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e38 (M.op X1 X0) (M.op X1 (M.op X2 X2))
             have i₂ := b1e12 X0 X1 X2
             grind)
          | exact superpose b1e12 b1e38
          | exact resolve b1e38 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e86 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 (M.op X1 X0) (M.op X1 (σ x))
             have i₂ := b1e38 X1 X0
             grind)
          | exact superpose b1e38 b1e38
          | exact resolve b1e38 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e93 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) X0) X1) X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op (σ x) X0) (σ x)
             have i₂ := b1e38 (σ x) X0
             grind)
          | exact superpose b1e38 b1e12
          | exact resolve b1e12 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e102 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ x)) := by
          intro X1 X2
          first
          | (have i₁ := b1e85 x X1 X2
             have i₂ := b1e86 x X1
             grind)
          | exact superpose b1e86 b1e85
          | exact resolve b1e85 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85
        have b1e124 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e40 X1 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b1e40 (M.op X0 X0) X0 X1
             grind)
          | exact superpose b1e40 b1e40
          | exact resolve b1e40 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e167 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op (M.op X0 X0) X1) = X1 := by
          intro X0 X1
          grind
        have b1e174 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X0 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e38 (σ x) X1
             have i₂ := b1e124 X0 (σ x)
             grind)
          | (have i₁ := b1e38 (σ x) X1
             have i₂ := b1e124 (σ x) X0
             grind)
          | exact superpose b1e124 b1e38
          | exact resolve b1e38 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e179 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b1e22
             have i₂ := b1e124 X0 (σ y)
             grind)
          | (have i₁ := b1e22
             have i₂ := b1e124 (σ y) X0
             grind)
          | exact superpose b1e124 b1e22
          | exact resolve b1e22 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e124
        have b1e182 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 := by
          intro X1
          first
          | (have i₁ := b1e174 x X1
             have i₂ := b1e102 (M.op (σ x) X1) x
             grind)
          | exact superpose b1e102 b1e174
          | exact resolve b1e174 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e174
        have b1e187 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e167 X0 X1
             have j1 := b1e15 (M.op X0 X0) X1
             grind)
          | (have r₁ := b1e167 X0 X1
             have r₂ := b1e15 (M.op X0 X0) X1
             grind)
          | exact resolve b1e167 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e167
        have b1e201 : ∀ X1 : G, (k (σ x) X1) = X1 := by
          intro X1
          first
          | (have i₁ := b1e187 x X1
             have i₂ := b1e179 x
             grind)
          | exact superpose b1e179 b1e187
          | exact resolve b1e187 b1e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e187
        have b1e243 : ∀ X0 : G, (τ (σ X0)) = (k (τ (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b1e34 (σ x) X0
             have i₂ := b1e201 (σ X0)
             grind)
          | exact superpose b1e201 b1e34
          | exact resolve b1e34 b1e201
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e201
        have b1e246 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b1e243 X0
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e243
          | exact resolve b1e243 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e243
        have b1e248 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e246 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e246
          | exact resolve b1e246 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e246
        have b1e262 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op X0 X0) ∨ (M.op x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e17 x X0
             have i₂ := b1e248 X0
             grind)
          | exact superpose b1e248 b1e17
          | (have j0 := b1e17 x X0
             grind)
          | exact resolve b1e17 b1e248
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e248
        have b1e265 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (M.op X0 X0) := by
          intro X0
          first
          | (have j0 := b1e262 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e262
        have b1e269 : ∀ X0 : G, (M.op x X0) = X0 ∨ x = (σ x) := by
          intro X0
          first
          | (have i₁ := b1e265 X0
             have i₂ := b1e179 X0
             grind)
          | exact superpose b1e179 b1e265
          | (have j0 := b1e265 X0
             grind)
          | exact resolve b1e265 b1e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e265
        have b1e294 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X4 X4))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b1e37 X2 (M.op (M.op (M.op X1 X1) X2) X0) X3 X4
             have i₂ := b1e40 X2 X1 X0
             grind)
          | exact superpose b1e40 b1e37
          | exact resolve b1e37 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37 b1e40
        have b1e387 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (σ x))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e294 X0 X1 X2 X3 x
             have i₂ := b1e102 X0 x
             grind)
          | exact superpose b1e102 b1e294
          | exact resolve b1e294 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e294
        have b1e429 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (σ x)) = (M.op X2 (M.op X0 (σ x))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e387 X0 X1 X2 x
             have i₂ := b1e102 (M.op (M.op (M.op X1 X1) X2) X0) x
             grind)
          | exact superpose b1e102 b1e387
          | exact resolve b1e387 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e387
        have b1e452 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (σ x))) = (M.op (M.op (M.op (σ x) X2) X0) (σ x)) := by
          intro X0 X2
          first
          | (have i₁ := b1e429 X0 x X2
             have i₂ := b1e179 x
             grind)
          | exact superpose b1e179 b1e429
          | exact resolve b1e429 b1e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e429
        have b1e979 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k (M.op (M.op (σ x) X0) X1) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e41 X0 (M.op (σ x) X1) (σ x)
             have i₂ := b1e38 (σ x) X1
             grind)
          | exact superpose b1e38 b1e41
          | (have r₁ := b1e41 X1 (M.op (σ x) X1) (σ x)
             have r₂ := b1e38 (σ x) X1
             grind)
          | (have r₁ := b1e41 (M.op (M.op X0 (M.op X1 (M.op x x))) (M.op X0 (σ x))) X1 x
             have r₂ := b1e38 X0 (M.op X1 (M.op x x))
             grind)
          | exact resolve b1e41 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e41
        have b1e1669 : x = (σ x) ∨ x = (σ x) := by
          first
          | (have i₁ := b1e179 x
             have i₂ := b1e269 x
             grind)
          | exact superpose b1e269 b1e179
          | exact resolve b1e179 b1e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e269
        have b1e1686 : x = (σ x) := by grind
        clear b1e1669
        have b1e1887 : (σ y) ≠ (M.op x (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e21
          | exact resolve b1e21 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1891 : y = (M.op y (M.op x x)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e43
          | exact resolve b1e43 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e1892 : ∀ X0 : G, (M.op (M.op x X0) x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e182 x
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e182
          | exact resolve b1e182 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e182
        have b1e1910 : y = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e1891
             have i₂ := b1e102 y x
             grind)
          | exact superpose b1e102 b1e1891
          | exact resolve b1e1891 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102 b1e1891
        have b1e1915 : y = (M.op y x) := by
          first
          | (have i₁ := b1e1910
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e1910
          | exact resolve b1e1910 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1910
        have b1e1964 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e93 X0 X1
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e93
          | exact resolve b1e93 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e93
        have b1e4306 : ∀ X0 : G, (k (M.op (M.op (σ x) X0) X0) X0) = X0 := by
          intro X0
          first
          | (have j0 := b1e979 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e979
        have b1e4307 : ∀ X0 : G, (k (M.op (M.op x X0) X0) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e4306 X0
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e4306
          | exact resolve b1e4306 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4306
        have b1e4343 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (M.op x (σ X0)) (σ X0))) X0) := by
          intro X0
          first
          | (have i₁ := b1e34 (M.op (M.op x (σ X0)) (σ X0)) X0
             have i₂ := b1e4307 (σ X0)
             grind)
          | exact superpose b1e4307 b1e34
          | exact resolve b1e34 b1e4307
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34 b1e4307
        have b1e4359 : ∀ X0 : G, (k (τ (M.op (M.op x (σ X0)) (σ X0))) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b1e4343 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e4343
          | exact resolve b1e4343 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4343
        have b1e7740 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op X1 (M.op X0 (M.op X1 (σ x)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e86 X1 (M.op (σ x) X0)
             have i₂ := b1e452 X1 X0
             grind)
          | exact superpose b1e452 b1e86
          | exact resolve b1e86 b1e452
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86 b1e452
        have b1e7774 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op X1 (M.op X0 (M.op X1 x))) := by
          intro X0 X1
          first
          | (have i₁ := b1e7740 X0 X1
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e7740
          | exact resolve b1e7740 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7740
        have b1e7817 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 x))) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e7774 X0 X1
             have i₂ := b1e1892 X0
             grind)
          | exact superpose b1e1892 b1e7774
          | exact resolve b1e7774 b1e1892
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1892 b1e7774
        have b1e7878 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e7817 X0 y
             have i₂ := b1e1915
             grind)
          | exact superpose b1e1915 b1e7817
          | exact resolve b1e7817 b1e1915
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1915 b1e7817
        have b1e8194 : ∀ X0 : G, y = (M.op X0 y) ∨ (k X0 y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e61 X0 y y
             have i₂ := b1e7878 y
             grind)
          | exact superpose b1e7878 b1e61
          | (have j0 := b1e61 X0 y x
             grind)
          | exact resolve b1e61 b1e7878
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e8207 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ y = (M.op X0 y) := by
          intro X0
          first
          | (have j0 := b1e8194 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e8194
        have b1e124210 : y = (M.op (τ (M.op (M.op x (σ y)) (σ y))) y) ∨ y = (M.op (τ (M.op (M.op x (σ y)) (σ y))) y) := by
          first
          | (have i₁ := b1e4359 y
             have i₂ := b1e8207 (τ (M.op (M.op x (σ y)) (σ y)))
             grind)
          | exact superpose b1e8207 b1e4359
          | (have j1 := b1e8207 (τ (M.op (M.op x (σ y)) (σ y)))
             grind)
          | exact resolve b1e4359 b1e8207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e4359 b1e8207
        have b1e124250 : y = (M.op (τ (M.op (M.op x (σ y)) (σ y))) y) := by grind
        clear b1e124210
        have b1e133712 : (M.op y y) = (τ (M.op (M.op x (σ y)) (σ y))) := by
          first
          | (have i₁ := b1e7878 (τ (M.op (M.op x (σ y)) (σ y)))
             have i₂ := b1e124250
             grind)
          | exact superpose b1e124250 b1e7878
          | exact resolve b1e7878 b1e124250
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e7878 b1e124250
        have b1e133772 : (σ x) = (τ (M.op (M.op x (σ y)) (σ y))) := by
          first
          | (have i₁ := b1e133712
             have i₂ := b1e179 y
             grind)
          | exact superpose b1e179 b1e133712
          | exact resolve b1e133712 b1e179
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e179 b1e133712
        have b1e133789 : x = (τ (M.op (M.op x (σ y)) (σ y))) := by
          first
          | (have i₁ := b1e133772
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e133772
          | exact resolve b1e133772 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133772
        have b1e134192 : (σ x) = (M.op (M.op x (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e14 (M.op (M.op x (σ y)) (σ y))
             have i₂ := b1e133789
             grind)
          | exact superpose b1e133789 b1e14
          | exact resolve b1e14 b1e133789
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e133789
        have b1e134216 : x = (M.op (M.op x (σ y)) (σ y)) := by
          first
          | (have i₁ := b1e134192
             have i₂ := b1e1686
             grind)
          | exact superpose b1e1686 b1e134192
          | exact resolve b1e134192 b1e1686
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1686 b1e134192
        have b1e134811 : (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b1e1964 (σ y) (σ y)
             have i₂ := b1e134216
             grind)
          | exact superpose b1e134216 b1e1964
          | exact resolve b1e1964 b1e134216
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1964 b1e134216
        have b1e134903 : False := by grind
        exact b1e134903
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e25 : y ≠ y ∨ y = (k x y) := by
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
        have b2e26 : y = (k x y) := by grind
        clear b2e25
        have b2e68 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
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
        have b2e284 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e68 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e285 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e284
             have r₂ := b2e21
             grind)
          | exact resolve b2e284 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e284
        have b2e286 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e285
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e285
          | exact resolve b2e285 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285
        have b2e287 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e286
             have i₂ := b2e26
             grind)
          | exact superpose b2e26 b2e286
          | exact resolve b2e286 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26 b2e286
        have b2e288 : False := by grind
        exact b2e288
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
             have i₂ := b3e12 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e54 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e59 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 (M.op X1 X1) X1
             have i₂ := b3e17 X0 (M.op X1 X1)
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 (M.op X1 (M.op X2 X2)) X1
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 (M.op X1 X1)
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e60 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b3e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e63 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e60 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e60 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e60 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60
        have b3e70 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e40 (M.op X1 X0) (M.op X1 (M.op X2 X2))
             have i₂ := b3e12 X0 X1 X2
             grind)
          | exact superpose b3e12 b3e40
          | exact resolve b3e40 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e71 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) x)) := by
          intro X0 X1
          first
          | (have i₁ := b3e40 (M.op X1 X0) (M.op X1 x)
             have i₂ := b3e40 X1 X0
             grind)
          | exact superpose b3e40 b3e40
          | exact resolve b3e40 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e76 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 (M.op x X0) x
             have i₂ := b3e40 x X0
             grind)
          | exact superpose b3e40 b3e12
          | exact resolve b3e12 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e81 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X1 x) (M.op X1 X0) X2
             have i₂ := b3e40 X1 X0
             grind)
          | exact superpose b3e40 b3e12
          | exact resolve b3e12 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e84 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
          intro X1 X2
          first
          | (have i₁ := b3e70 x X1 X2
             have i₂ := b3e71 x X1
             grind)
          | exact superpose b3e71 b3e70
          | exact resolve b3e70 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e71
        have b3e93 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e29 X0 X1
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e97 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
          intro X0
          first
          | (have i₁ := b3e76 X0 (M.op x x)
             have i₂ := b3e40 x X0
             grind)
          | exact superpose b3e40 b3e76
          | exact resolve b3e76 b3e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e100 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op x X1) X0) (M.op X2 X2))) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 (M.op (M.op x X1) X0) X2
             have i₂ := b3e76 X1 X0
             grind)
          | exact superpose b3e76 b3e12
          | exact resolve b3e12 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e105 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
          intro X1
          first
          | (have i₁ := b3e100 x X1 x
             have i₂ := b3e81 x (M.op x X1) x
             grind)
          | exact superpose b3e81 b3e100
          | exact resolve b3e100 b3e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e100
        have b3e128 : ∀ X0 : G, (k (M.op x x) X0) = X0 ∨ (M.op (M.op x x) X0) = X0 := by
          intro X0
          grind
        have b3e130 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e40 X0 X0
             have i₂ := b3e97 X0
             grind)
          | (have i₁ := b3e40 x x
             have i₂ := b3e97 X0
             grind)
          | exact superpose b3e97 b3e40
          | exact resolve b3e40 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e135 : x = (M.op x x) := by
          first
          | (have i₁ := b3e40 x x
             have i₂ := b3e97 (M.op x x)
             grind)
          | exact superpose b3e97 b3e40
          | exact resolve b3e40 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e138 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) x) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e76 x X1
             have i₂ := b3e97 X0
             grind)
          | (have i₁ := b3e76 x X1
             have i₂ := b3e97 x
             grind)
          | exact superpose b3e97 b3e76
          | exact resolve b3e76 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e142 : ∀ X0 : G, x = (M.op (M.op X0 X0) (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e40 X0 X0
             have i₂ := b3e97 X0
             grind)
          | (have i₁ := b3e40 x x
             have i₂ := b3e97 X0
             grind)
          | exact superpose b3e97 b3e40
          | exact resolve b3e40 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e146 : ∀ X0 : G, x = (M.op (M.op X0 X0) x) := by
          intro X0
          first
          | (have i₁ := b3e142 X0
             have i₂ := b3e84 (M.op X0 X0) X0
             grind)
          | exact superpose b3e84 b3e142
          | exact resolve b3e142 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e142
        have b3e152 : ∀ X0 : G, (M.op x (M.op X0 x)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e130 X0
             have i₂ := b3e135
             grind)
          | exact superpose b3e135 b3e130
          | exact resolve b3e130 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e130
        have b3e153 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
          intro X0
          first
          | (have j0 := b3e128 X0
             have j1 := b3e15 (M.op x x) X0
             grind)
          | (have r₁ := b3e128 x
             have r₂ := b3e15 (M.op x x) x
             grind)
          | exact resolve b3e128 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e158 : ∀ X0 : G, (k x X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e153 X0
             have i₂ := b3e135
             grind)
          | exact superpose b3e135 b3e153
          | exact resolve b3e153 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e153
        have b3e173 : ∀ X0 : G, x = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b3e42 X0 x x
             have i₂ := b3e76 x X0
             grind)
          | exact superpose b3e76 b3e42
          | exact resolve b3e42 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42 b3e76
        have b3e1250 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e51 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e1252 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b3e1250 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1250
        have b3e1279 : ∀ X0 : G, (σ X0) = (M.op x x) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e1252 X0
             have i₂ := b3e97 (σ X0)
             grind)
          | exact superpose b3e97 b3e1252
          | (have j0 := b3e1252 X0
             grind)
          | exact resolve b3e1252 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e97 b3e1252
        have b3e1343 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = x := by
          intro X0
          first
          | (have i₁ := b3e1279 X0
             have i₂ := b3e135
             grind)
          | exact superpose b3e135 b3e1279
          | (have j0 := b3e1279 X0
             grind)
          | exact resolve b3e1279 b3e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e135 b3e1279
        have b3e1563 : ∀ X0 X1 : G, x = X0 ∨ (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) = (k (M.op (M.op X1 X1) X0) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e173 (M.op (M.op X1 X1) X0)
             have i₂ := b3e59 (M.op (M.op X1 X1) X0) X1 X0
             grind)
          | exact superpose b3e59 b3e173
          | (have j1 := b3e59 (M.op (M.op X1 X1) X0) X1 x
             grind)
          | exact resolve b3e173 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e1595 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (k (M.op x X0) x) ∨ x = X0 ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1563 X0 X0
             have i₂ := b3e173 X0
             grind)
          | exact superpose b3e173 b3e1563
          | (have j0 := b3e1563 X0 X1
             grind)
          | exact resolve b3e1563 b3e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1563
        have b3e1645 : ∀ X0 X1 : G, (k (M.op x X0) x) = X0 ∨ x = X0 ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1595 X0 X1
             have i₂ := b3e105 X0
             grind)
          | (have i₁ := b3e1595 X0 X1
             have i₂ := b3e105 (M.op (M.op x X0) x)
             grind)
          | exact superpose b3e105 b3e1595
          | (have j0 := b3e1595 X0 X1
             grind)
          | exact resolve b3e1595 b3e105
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e105 b3e1595
        have b3e1688 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) x) ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1645 X0 X1
             have i₂ := b3e84 (M.op (M.op X1 X1) X0) X1
             grind)
          | exact superpose b3e84 b3e1645
          | (have j0 := b3e1645 X0 X1
             grind)
          | exact resolve b3e1645 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84 b3e1645
        have b3e1726 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e1688 X0 X1
             have i₂ := b3e138 X1 X0
             grind)
          | exact superpose b3e138 b3e1688
          | (have j0 := b3e1688 X0 X1
             grind)
          | exact resolve b3e1688 b3e138
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e138 b3e1688
        have b3e1759 : ∀ X0 : G, x = X0 ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have i₁ := b3e1726 X0 x
             have i₂ := b3e173 x
             grind)
          | exact superpose b3e173 b3e1726
          | (have j0 := b3e1726 X0 x
             grind)
          | exact resolve b3e1726 b3e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1726
        have b3e1760 : ∀ X0 : G, (k (M.op x X0) x) = X0 ∨ x = X0 := by
          intro X0
          first
          | (have j0 := b3e1759 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1759
        have b3e2241 : ∀ X0 : G, (τ (σ X0)) = (k (τ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e93 x X0
             have i₂ := b3e158 (σ X0)
             grind)
          | exact superpose b3e158 b3e93
          | exact resolve b3e93 b3e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2245 : ∀ X0 : G, (k (τ x) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2241 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e2241
          | exact resolve b3e2241 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2241
        have b3e2275 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ x)) X0) := by
          intro X0
          first
          | (have i₁ := b3e93 (τ x) X0
             have i₂ := b3e2245 (σ X0)
             grind)
          | exact superpose b3e2245 b3e93
          | exact resolve b3e93 b3e2245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93 b3e2245
        have b3e2288 : ∀ X0 : G, (k (τ (τ x)) X0) = X0 := by
          intro X0
          first
          | (have i₁ := b3e2275 X0
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e2275
          | exact resolve b3e2275 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2275
        have b3e2648 : (σ (τ (τ x))) ≠ (σ (τ (τ x))) ∨ x = (σ (τ (τ x))) := by
          first
          | (have i₁ := b3e1343 (τ (τ x))
             have i₂ := b3e2288 (τ (τ x))
             grind)
          | exact superpose b3e2288 b3e1343
          | (have j0 := b3e1343 (τ (τ x))
             grind)
          | exact resolve b3e1343 b3e2288
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2288
        have b3e2651 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
          first
          | (have i₁ := b3e1343 x
             have i₂ := b3e158 x
             grind)
          | exact superpose b3e158 b3e1343
          | (have j0 := b3e1343 x
             grind)
          | exact resolve b3e1343 b3e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e158 b3e1343
        have b3e2655 : x = (σ x) := by grind
        clear b3e2651
        have b3e2658 : x = (σ (τ (τ x))) := by grind
        clear b3e2648
        have b3e2670 : x = (τ x) := by
          first
          | (have i₁ := b3e2658
             have i₂ := b3e14 (τ x)
             grind)
          | exact superpose b3e14 b3e2658
          | exact resolve b3e2658 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2658
        have b3e2698 : (σ y) = (M.op x (σ y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e2655
             grind)
          | exact superpose b3e2655 b3e22
          | exact resolve b3e22 b3e2655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2707 : ∀ X0 : G, (k (σ X0) x) = (σ (k X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 x
             have i₂ := b3e2655
             grind)
          | exact superpose b3e2655 b3e18
          | exact resolve b3e18 b3e2655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2655
        have b3e6080 : (σ y) = (k (σ y) x) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e1760 (σ y)
             have i₂ := b3e2698
             grind)
          | exact superpose b3e2698 b3e1760
          | (have j0 := b3e1760 (σ y)
             grind)
          | exact resolve b3e1760 b3e2698
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1760 b3e2698
        have b3e6101 : (σ y) = (σ (k y x)) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e6080
             have i₂ := b3e2707 y
             grind)
          | exact superpose b3e2707 b3e6080
          | exact resolve b3e6080 b3e2707
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2707 b3e6080
        have b3e12083 : (τ (σ y)) = (k y x) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e13 (k y x)
             have i₂ := b3e6101
             grind)
          | exact superpose b3e6101 b3e13
          | exact resolve b3e13 b3e6101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e6101
        have b3e12120 : y = (k y x) ∨ x = (σ y) := by
          first
          | (have i₁ := b3e12083
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e12083
          | exact resolve b3e12083 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e12083
        have b3e12137 : y = (M.op y x) ∨ x = y ∨ x = (σ y) := by
          first
          | (have i₁ := b3e63 y x
             have i₂ := b3e12120
             grind)
          | exact superpose b3e12120 b3e63
          | exact resolve b3e63 b3e12120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e12120
        have b3e63377 : y = (M.op x y) ∨ x = y ∨ x = (σ y) := by
          first
          | (have i₁ := b3e152 y
             have i₂ := b3e12137
             grind)
          | exact superpose b3e12137 b3e152
          | exact resolve b3e152 b3e12137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e152 b3e12137
        have b3e63457 : x = (σ y) ∨ x = y := by
          first
          | (have r₁ := b3e63377
             have r₂ := b3e20
             grind)
          | exact resolve b3e63377 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63377
        have b3e64373 : y = (τ x) ∨ x = y := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e63457
             grind)
          | exact superpose b3e63457 b3e13
          | exact resolve b3e13 b3e63457
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63457
        have b3e64455 : x = y ∨ x = y := by
          first
          | (have i₁ := b3e64373
             have i₂ := b3e2670
             grind)
          | exact superpose b3e2670 b3e64373
          | exact resolve b3e64373 b3e2670
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2670 b3e64373
        have b3e64456 : x = y := by grind
        clear b3e64455
        have b3e65814 : ∀ X0 : G, y = (M.op (M.op X0 X0) y) := by
          intro X0
          first
          | (have i₁ := b3e146 X0
             have i₂ := b3e64456
             grind)
          | exact superpose b3e64456 b3e146
          | exact resolve b3e146 b3e64456
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146 b3e64456
        have b3e65963 : y = (M.op x y) := by
          first
          | (have i₁ := b3e65814 x
             have i₂ := b3e173 x
             grind)
          | exact superpose b3e173 b3e65814
          | exact resolve b3e65814 b3e173
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e173 b3e65814
        have b3e66006 : False := by grind
        exact b3e66006
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e35 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e13 y y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (σ x))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
               have i₂ := b4e13 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : y = (M.op x (M.op y (σ x))) := by
            first
            | (have i₁ := b4e35 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e35
            | exact resolve b4e35 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : y = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e35 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e63 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e69 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X0) = X2 ∨ (M.op X0 (M.op X1 X1)) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op X0 (M.op X1 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) X1
               have i₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | (have i₁ := b4e13 X0 X1 X2
               have i₂ := b4e18 (M.op X1 (M.op X2 X2)) X1
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X0 (M.op X1 X1)
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e71 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e63 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e74 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e71 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e71 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e71 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e75 : ∀ X0 : G, (M.op y x) = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op y x) x X0
               have i₂ := b4e45
               grind)
            | exact superpose b4e45 b4e13
            | exact resolve b4e13 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45
          have b4e78 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 (M.op X1 X0) (M.op X1 (M.op X2 X2))
               have i₂ := b4e13 X0 X1 X2
               grind)
            | exact superpose b4e13 b4e38
            | exact resolve b4e38 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e79 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 (M.op X1 X0) (M.op X1 x)
               have i₂ := b4e38 X1 X0
               grind)
            | exact superpose b4e38 b4e38
            | exact resolve b4e38 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e90 : ∀ X0 X1 X2 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op X1 x) (M.op X1 X0) X2
               have i₂ := b4e38 X1 X0
               grind)
            | exact superpose b4e38 b4e13
            | exact resolve b4e13 b4e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e94 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
            intro X1 X2
            first
            | (have i₁ := b4e78 x X1 X2
               have i₂ := b4e79 x X1
               grind)
            | exact superpose b4e79 b4e78
            | exact resolve b4e78 b4e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e96 : ∀ X0 : G, (M.op y (σ x)) = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e13 (M.op y (σ x)) x X0
               have i₂ := b4e44
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e98 : (M.op y (σ x)) = (M.op y x) := by
            first
            | (have i₁ := b4e96 x
               have i₂ := b4e75 x
               grind)
            | exact superpose b4e75 b4e96
            | exact resolve b4e96 b4e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e75 b4e96
          have b4e113 : ∀ X0 : G, (σ x) = (M.op (M.op y x) (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) y X0
               have i₂ := b4e98
               grind)
            | exact superpose b4e98 b4e13
            | exact resolve b4e13 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98
          have b4e115 : x = (σ x) := by
            first
            | (have i₁ := b4e113 x
               have i₂ := b4e13 x y x
               grind)
            | exact superpose b4e13 b4e113
            | exact resolve b4e113 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e113
          have b4e167 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e115
               grind)
            | exact superpose b4e115 b4e20
            | exact resolve b4e20 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e169 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e115
               grind)
            | exact superpose b4e115 b4e19
            | exact resolve b4e19 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e186 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b4e41 (M.op X0 X0) X0 X1
               grind)
            | exact superpose b4e41 b4e41
            | exact resolve b4e41 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e190 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3))) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 X2 (M.op (M.op (M.op X1 X1) X2) X0) X3
               have i₂ := b4e41 X2 X1 X0
               grind)
            | exact superpose b4e41 b4e13
            | exact resolve b4e13 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e197 : ∀ X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) x) = X2 := by
            intro X1 X2
            first
            | (have i₁ := b4e190 x X1 X2 x
               have i₂ := b4e90 x (M.op (M.op X1 X1) X2) x
               grind)
            | exact superpose b4e90 b4e190
            | exact resolve b4e190 b4e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e90 b4e190
          have b4e253 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 x)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X1 X1
               have i₂ := b4e186 X0 X1
               grind)
            | (have i₁ := b4e38 X1 X1
               have i₂ := b4e186 X1 X0
               grind)
            | exact superpose b4e186 b4e38
            | exact resolve b4e38 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e264 : ∀ X0 X1 : G, (M.op (M.op x X1) (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e38 x X1
               have i₂ := b4e186 X0 x
               grind)
            | (have i₁ := b4e38 x X1
               have i₂ := b4e186 x X0
               grind)
            | exact superpose b4e186 b4e38
            | exact resolve b4e38 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e265 : ∀ X0 : G, x = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e186 X0 y
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e186 y X0
               grind)
            | exact superpose b4e186 b4e22
            | exact resolve b4e22 b4e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186
          have b4e266 : ∀ X1 : G, (M.op (M.op x X1) x) = X1 := by
            intro X1
            first
            | (have i₁ := b4e264 x X1
               have i₂ := b4e94 (M.op x X1) x
               grind)
            | exact superpose b4e94 b4e264
            | exact resolve b4e264 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e264
          have b4e275 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
            intro X1
            first
            | (have i₁ := b4e253 x X1
               have i₂ := b4e265 x
               grind)
            | exact superpose b4e265 b4e253
            | exact resolve b4e253 b4e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e253
          have b4e362 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e74 (σ X0) (σ X1)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e74
            | exact resolve b4e74 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e404 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X4 X4))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e37 X2 (M.op (M.op (M.op X1 X1) X2) X0) X3 X4
               have i₂ := b4e41 X2 X1 X0
               grind)
            | exact superpose b4e41 b4e37
            | exact resolve b4e37 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e41
          have b4e511 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3)) = (M.op X2 (M.op X0 x)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e404 X0 X1 X2 X3 x
               have i₂ := b4e94 X0 x
               grind)
            | exact superpose b4e94 b4e404
            | exact resolve b4e404 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e404
          have b4e562 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) x) = (M.op X2 (M.op X0 x)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e511 X0 X1 X2 x
               have i₂ := b4e94 (M.op (M.op (M.op X1 X1) X2) X0) x
               grind)
            | exact superpose b4e94 b4e511
            | exact resolve b4e511 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e511
          have b4e589 : ∀ X0 X2 : G, (M.op X2 (M.op X0 x)) = (M.op (M.op (M.op x X2) X0) x) := by
            intro X0 X2
            first
            | (have i₁ := b4e562 X0 x X2
               have i₂ := b4e265 x
               grind)
            | exact superpose b4e265 b4e562
            | exact resolve b4e562 b4e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e562
          have b4e1702 : ∀ X0 X1 : G, x = X0 ∨ (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) = (k (M.op (M.op X1 X1) X0) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e265 (M.op (M.op X1 X1) X0)
               have i₂ := b4e69 (M.op (M.op X1 X1) X0) X1 X0
               grind)
            | exact superpose b4e69 b4e265
            | (have j1 := b4e69 (M.op (M.op X1 X1) X0) X1 x
               grind)
            | exact resolve b4e265 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e1738 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (k (M.op x X0) x) ∨ x = X0 ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1702 X0 X0
               have i₂ := b4e265 X0
               grind)
            | exact superpose b4e265 b4e1702
            | (have j0 := b4e1702 X0 X1
               grind)
            | exact resolve b4e1702 b4e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1702
          have b4e1790 : ∀ X0 X1 : G, (k (M.op x X0) x) = X0 ∨ x = X0 ∨ (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1738 X0 X1
               have i₂ := b4e266 X0
               grind)
            | (have i₁ := b4e1738 X0 X1
               have i₂ := b4e266 (M.op (M.op x X0) x)
               grind)
            | exact superpose b4e266 b4e1738
            | (have j0 := b4e1738 X0 X1
               grind)
            | exact resolve b4e1738 b4e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1738
          have b4e1836 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 X1) X0) x) ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1790 X0 X1
               have i₂ := b4e94 (M.op (M.op X1 X1) X0) X1
               grind)
            | exact superpose b4e94 b4e1790
            | (have j0 := b4e1790 X0 X1
               grind)
            | exact resolve b4e1790 b4e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94 b4e1790
          have b4e1877 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e1836 X0 X1
               have i₂ := b4e197 X1 X0
               grind)
            | (have i₁ := b4e1836 X0 X1
               have i₂ := b4e197 X1 (M.op (M.op (M.op X1 X1) X0) x)
               grind)
            | exact superpose b4e197 b4e1836
            | (have j0 := b4e1836 X0 X1
               grind)
            | exact resolve b4e1836 b4e197
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e197 b4e1836
          have b4e1909 : ∀ X0 : G, x = X0 ∨ (k (M.op x X0) x) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e1877 X0 x
               have i₂ := b4e265 x
               grind)
            | exact superpose b4e265 b4e1877
            | (have j0 := b4e1877 X0 x
               grind)
            | exact resolve b4e1877 b4e265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e265 b4e1877
          have b4e1910 : ∀ X0 : G, (k (M.op x X0) x) = X0 ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b4e1909 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1909
          have b4e3898 : ∀ X0 X1 : G, (M.op (M.op x X0) x) = (M.op X1 (M.op X0 (M.op X1 x))) := by
            intro X0 X1
            first
            | (have i₁ := b4e79 X1 (M.op x X0)
               have i₂ := b4e589 X1 X0
               grind)
            | exact superpose b4e589 b4e79
            | exact resolve b4e79 b4e589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e3904 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x X0) X1) X2) (M.op X0 (M.op X1 x))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e38 (M.op (M.op x X0) X1) X2
               have i₂ := b4e589 X1 X0
               grind)
            | exact superpose b4e589 b4e38
            | exact resolve b4e38 b4e589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38 b4e589
          have b4e3933 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 x))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e3898 X0 X1
               have i₂ := b4e266 X0
               grind)
            | (have i₁ := b4e3898 X0 X1
               have i₂ := b4e266 (M.op (M.op x X0) x)
               grind)
            | exact superpose b4e266 b4e3898
            | exact resolve b4e3898 b4e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3898
          have b4e6420 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (k X0 x))) = X1 ∨ (σ x) = (σ (k X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e39 (σ X0) X1
               have i₂ := b4e362 X0 x
               grind)
            | exact superpose b4e362 b4e39
            | (have j1 := b4e362 X0 x
               grind)
            | exact resolve b4e39 b4e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e362
          have b4e6474 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (k X0 x))) = X1 ∨ x = (σ (k X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6420 X0 X1
               have i₂ := b4e115
               grind)
            | exact superpose b4e115 b4e6420
            | (have j0 := b4e6420 X0 X1
               grind)
            | exact resolve b4e6420 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6420
          have b4e142127 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) (k X0 (σ x))) = X1 ∨ x = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6474 (τ X0) X1
               have i₂ := b4e29 X0 x
               grind)
            | exact superpose b4e29 b4e6474
            | exact resolve b4e6474 b4e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29 b4e6474
          have b4e142264 : ∀ X0 X1 : G, (M.op (M.op (σ (τ X0)) X1) (k X0 x)) = X1 ∨ x = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142127 X0 X1
               have i₂ := b4e115
               grind)
            | exact superpose b4e115 b4e142127
            | (have j0 := b4e142127 X0 X1
               grind)
            | exact resolve b4e142127 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142127
          have b4e142341 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 x)) = X1 ∨ x = (k X0 (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e142264 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e142264
            | (have j0 := b4e142264 X0 X1
               grind)
            | exact resolve b4e142264 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142264
          have b4e142396 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X0 x)) = X1 ∨ x = (k X0 x) := by
            intro X0 X1
            first
            | (have i₁ := b4e142341 X0 X1
               have i₂ := b4e115
               grind)
            | exact superpose b4e115 b4e142341
            | (have j0 := b4e142341 X0 X1
               grind)
            | exact resolve b4e142341 b4e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e115 b4e142341
          have b4e181217 : ∀ X0 X1 : G, (k (M.op x X1) x) = (M.op X0 (M.op X1 (M.op X0 x))) ∨ x = (k (M.op x X1) x) := by
            intro X0 X1
            first
            | (have i₁ := b4e3904 X1 X0 (k (M.op x X1) x)
               have i₂ := b4e142396 (M.op x X1) X0
               grind)
            | exact superpose b4e142396 b4e3904
            | (have j1 := b4e142396 (M.op x X1) X1
               grind)
            | exact resolve b4e3904 b4e142396
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3904 b4e142396
          have b4e181255 : ∀ X1 : G, (k (M.op x X1) x) = X1 ∨ x = (k (M.op x X1) x) := by
            intro X1
            first
            | (have i₁ := b4e181217 x X1
               have i₂ := b4e3933 X1 x
               grind)
            | exact superpose b4e3933 b4e181217
            | (have j0 := b4e181217 x X1
               grind)
            | exact resolve b4e181217 b4e3933
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3933 b4e181217
          have b4e193693 : ∀ X0 : G, x ≠ X0 ∨ (k (M.op x X0) x) = X0 := by
            intro X0
            first
            | (have j0 := b4e181255 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e181255
          have b4e193754 : ∀ X0 : G, (k (M.op x X0) x) = X0 := by
            intro X0
            first
            | (have j0 := b4e193693 X0
               have j1 := b4e1910 X0
               grind)
            | (have r₁ := b4e193693 (k (M.op x x) x)
               have r₂ := b4e1910 x
               grind)
            | (have r₁ := b4e193693 X0
               have r₂ := b4e1910 X0
               grind)
            | (have r₁ := b4e193693 x
               have r₂ := b4e1910 x
               grind)
            | exact resolve b4e193693 b4e1910
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1910 b4e193693
          have b4e194533 : ∀ X0 : G, (M.op X0 x) = (k X0 x) := by
            intro X0
            first
            | (have i₁ := b4e193754 (M.op X0 x)
               have i₂ := b4e275 X0
               grind)
            | exact superpose b4e275 b4e193754
            | exact resolve b4e193754 b4e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e193754
          have b4e195366 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b4e169 X0
               have i₂ := b4e194533 (σ X0)
               grind)
            | exact superpose b4e194533 b4e169
            | exact resolve b4e169 b4e194533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e169
          have b4e195497 : ∀ X0 : G, (M.op (σ X0) x) = (σ (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e195366 X0
               have i₂ := b4e194533 X0
               grind)
            | exact superpose b4e194533 b4e195366
            | exact resolve b4e195366 b4e194533
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194533 b4e195366
          have b4e197286 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op x X0)) x) := by
            intro X0
            first
            | (have i₁ := b4e195497 (M.op x X0)
               have i₂ := b4e266 X0
               grind)
            | exact superpose b4e266 b4e195497
            | exact resolve b4e195497 b4e266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e266 b4e195497
          have b4e199492 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e275 (σ (M.op x X0))
               have i₂ := b4e197286 X0
               grind)
            | exact superpose b4e197286 b4e275
            | exact resolve b4e275 b4e197286
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e275 b4e197286
          have b4e201600 : (M.op x (σ y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b4e167
               have i₂ := b4e199492 y
               grind)
            | exact superpose b4e199492 b4e167
            | (have r₁ := b4e167
               have r₂ := b4e199492 y
               grind)
            | exact resolve b4e167 b4e199492
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e167 b4e199492
          have b4e201684 : False := by grind
          exact b4e201684
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e43 : y = (k x y) ∨ y = (M.op x y) := by grind
          have b5e46 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e21
               grind)
            | exact resolve b5e43 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e43
          have b5e61 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) := by
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
          have b5e480 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e61 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e481 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e480
               have r₂ := b5e23
               grind)
            | exact resolve b5e480 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e480
          have b5e482 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e481
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e481
            | exact resolve b5e481 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e481
          have b5e483 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e482
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e482
            | exact resolve b5e482 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e482
          have b5e484 : False := by grind
          exact b5e484
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e25 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e25
        have b6e27 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b6e26
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e26
          | exact resolve b6e26 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e32 : (k x y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e27
             grind)
          | exact superpose b6e27 b6e13
          | exact resolve b6e13 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e33 : y = (k x y) := by
          first
          | (have i₁ := b6e32
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e32
          | exact resolve b6e32 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e32
        have b6e53 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
        have b6e62 : y = (M.op x y) ∨ x = (M.op y y) := by grind
        clear b6e53
        have b6e66 : x = (M.op y y) := by
          first
          | (have r₁ := b6e62
             have r₂ := b6e20
             grind)
          | exact resolve b6e62 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62
        have b6e69 : False := by grind
        exact b6e69
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e40 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          have b7e43 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e40
               have r₂ := b7e23
               grind)
            | exact resolve b7e40 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
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
          have b7e70 : y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e48
               grind)
            | exact superpose b7e48 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e71 : y = (M.op x y) ∨ x = (M.op y y) := by grind
          clear b7e70
          have b7e73 : x = (M.op y y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e75 : False := by grind
          exact b7e75
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e513 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e52 x y
               grind)
            | exact superpose b8e52 b8e20
            | (have j1 := b8e52 x y
               grind)
            | exact resolve b8e20 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e612 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e513
               have r₂ := b8e24
               grind)
            | exact resolve b8e513 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e513
          have b8e620 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e612
               have r₂ := b8e23
               grind)
            | exact resolve b8e612 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e612
          have b8e623 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e620
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e620
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e620 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e620
          have b8e624 : x = (M.op y y) ∨ y = (M.op x y) := by grind
          clear b8e623
          have b8e626 : y = (M.op x y) := by
            first
            | (have r₁ := b8e624
               have r₂ := b8e22
               grind)
            | exact resolve b8e624 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e624
          have b8e627 : False := by grind
          exact b8e627

/-- `Equation1496`: `x = (y ◇ x) ◇ (y ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then Y else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_y_y_pyx_Equation1496 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1496 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1496.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = b :=
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
    · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b0e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b0e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b0e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y x) := by grind
        have b0e22 : x = (M.op x y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e19
          | exact resolve b0e19 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e26 : x ≠ x ∨ x = (k y x) := by
          first
          | (have i₁ := b0e15 y x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have j0 := b0e15 y x
             grind)
          | (have r₁ := b0e15 y x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e29 : x = (k y x) := by grind
        clear b0e26
        have b0e32 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 (τ X0) X1
             have i₂ := b0e14 X0
             grind)
          | exact superpose b0e14 b0e18
          | exact resolve b0e18 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b0e12 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
             have i₂ := b0e12 X0 X1 X2
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e36 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 y x X0
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e12
          | exact resolve b0e12 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e37 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b0e12 x y X0
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e12 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
             have i₂ := b0e12 X0 (M.op X1 X1) X1
             grind)
          | exact superpose b0e12 b0e12
          | exact resolve b0e12 b0e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b0e18 X1 X0
             have i₂ := b0e17 (σ X1) (σ X0)
             grind)
          | exact superpose b0e17 b0e18
          | (have j1 := b0e17 (σ X1) (σ X0)
             grind)
          | exact resolve b0e18 b0e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e75 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b0e13 (k (τ X0) X1)
             have i₂ := b0e32 X0 X1
             grind)
          | exact superpose b0e32 b0e13
          | exact resolve b0e13 b0e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e32
        have b0e93 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e39 X1 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b0e39 (M.op X0 X0) X0 X1
             grind)
          | exact superpose b0e39 b0e39
          | exact resolve b0e39 b0e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e122 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          grind
        have b0e130 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b0e122 X0 X1
             have j1 := b0e15 (M.op X0 X0) X1
             grind)
          | (have r₁ := b0e122 X0 X1
             have r₂ := b0e15 (M.op X0 X0) X1
             grind)
          | exact resolve b0e122 b0e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e122
        have b0e198 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X0)) = (M.op (M.op y (M.op X1 X1)) (M.op x (M.op X2 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e34 (M.op y (M.op X1 X1)) y X0 X2
             have i₂ := b0e37 X1
             grind)
          | exact superpose b0e37 b0e34
          | exact resolve b0e34 b0e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e211 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op X1 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b0e34 x X0 X2 x
             have i₂ := b0e34 x X0 X1 x
             grind)
          | (have i₁ := b0e34 X1 X1 X2 X1
             have i₂ := b0e34 X0 X1 (M.op X1 X1) x
             grind)
          | exact superpose b0e34 b0e34
          | exact resolve b0e34 b0e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e233 : ∀ X0 X1 : G, x = (M.op y (M.op X0 (M.op (M.op y X0) (M.op X1 X1)))) := by
          intro X0 X1
          first
          | (have i₁ := b0e37 x
             have i₂ := b0e34 X0 y x X1
             grind)
          | (have i₁ := b0e37 (M.op y y)
             have i₂ := b0e34 y y x y
             grind)
          | exact superpose b0e34 b0e37
          | exact resolve b0e37 b0e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e34 b0e37
        have b0e299 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e75 (M.op X1 X1) X0
             have i₂ := b0e130 X1 (σ X0)
             grind)
          | exact superpose b0e130 b0e75
          | exact resolve b0e75 b0e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e130
        have b0e309 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b0e299 X0 X1
             have i₂ := b0e13 X0
             grind)
          | exact superpose b0e13 b0e299
          | exact resolve b0e299 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e299
        have b0e336 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e75 (τ (M.op X1 X1)) X0
             have i₂ := b0e309 (σ X0) X1
             grind)
          | exact superpose b0e309 b0e75
          | exact resolve b0e75 b0e309
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e75 b0e309
        have b0e339 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b0e336 X0 X1
             have i₂ := b0e13 X0
             grind)
          | exact superpose b0e13 b0e336
          | exact resolve b0e336 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e336
        have b0e568 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b0e51 X0 X0
             have i₂ := b0e93 X0 (σ X0)
             grind)
          | (have i₁ := b0e51 X0 X0
             have i₂ := b0e93 (σ X0) X1
             grind)
          | exact superpose b0e93 b0e51
          | exact resolve b0e51 b0e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e646 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b0e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e51
        have b0e670 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have j0 := b0e568 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e568
        have b0e5301 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b0e670 X1 (τ (τ (M.op X0 X0)))
             have i₂ := b0e339 (τ (τ (M.op X0 X0))) X0
             grind)
          | exact superpose b0e339 b0e670
          | (have j0 := b0e670 X1 (τ (τ (M.op X0 X0)))
             grind)
          | exact resolve b0e670 b0e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e339 b0e670
        have b0e5481 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have j0 := b0e5301 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e5301
        have b0e5530 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b0e5481 X0 X1
             have i₂ := b0e14 (τ (M.op X0 X0))
             grind)
          | exact superpose b0e14 b0e5481
          | exact resolve b0e5481 b0e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e5481
        have b0e6182 : ∀ X0 : G, x = (M.op y (M.op y (τ (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b0e233 y y
             have i₂ := b0e5530 X0 (M.op y y)
             grind)
          | exact superpose b0e5530 b0e233
          | exact resolve b0e233 b0e5530
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e233 b0e5530
        have b0e26364 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b0e646 x y
             have i₂ := b0e29
             grind)
          | exact superpose b0e29 b0e646
          | (have j0 := b0e646 x y
             grind)
          | exact resolve b0e646 b0e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e29 b0e646
        have b0e26373 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b0e26364
        have b0e26399 : (σ y) = (M.op (σ x) (σ x)) := by
          first
          | (have r₁ := b0e26373
             have r₂ := b0e24
             grind)
          | exact resolve b0e26373 b0e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26373
        have b0e26435 : y = (M.op x (M.op x (σ y))) := by
          first
          | (have i₁ := b0e36 (σ x)
             have i₂ := b0e26399
             grind)
          | exact superpose b0e26399 b0e36
          | exact resolve b0e36 b0e26399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e36
        have b0e26448 : ∀ X0 : G, (σ y) = (M.op X0 X0) := by
          intro X0
          first
          | (have i₁ := b0e93 (σ x) X0
             have i₂ := b0e26399
             grind)
          | exact superpose b0e26399 b0e93
          | exact resolve b0e93 b0e26399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e93
        have b0e26476 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op (M.op y (σ y)) (M.op x (M.op X1 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b0e198 X0 (σ x) X1
             have i₂ := b0e26399
             grind)
          | exact superpose b0e26399 b0e198
          | exact resolve b0e198 b0e26399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e198
        have b0e26479 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b0e211 X0 (σ x) X1
             have i₂ := b0e26399
             grind)
          | exact superpose b0e26399 b0e211
          | exact resolve b0e211 b0e26399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e211
        have b0e26559 : x = (M.op y (M.op y (τ (σ y)))) := by
          first
          | (have i₁ := b0e6182 (σ x)
             have i₂ := b0e26399
             grind)
          | exact superpose b0e26399 b0e6182
          | exact resolve b0e6182 b0e26399
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e6182 b0e26399
        have b0e26614 : x = (M.op y (M.op y y)) := by
          first
          | (have i₁ := b0e26559
             have i₂ := b0e13 y
             grind)
          | exact superpose b0e13 b0e26559
          | exact resolve b0e26559 b0e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26559
        have b0e26629 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (M.op y (σ y)) (M.op x (σ y))) := by
          intro X0
          first
          | (have i₁ := b0e26476 X0 x
             have i₂ := b0e26479 x x
             grind)
          | exact superpose b0e26479 b0e26476
          | exact resolve b0e26476 b0e26479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26476
        have b0e26670 : x = (M.op y (σ y)) := by
          first
          | (have i₁ := b0e26614
             have i₂ := b0e26479 y y
             grind)
          | exact superpose b0e26479 b0e26614
          | exact resolve b0e26614 b0e26479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26614
        have b0e26677 : (M.op y (σ y)) = (M.op (M.op y (σ y)) (M.op x (σ y))) := by
          first
          | (have i₁ := b0e26629 x
             have i₂ := b0e26479 y x
             grind)
          | exact superpose b0e26479 b0e26629
          | exact resolve b0e26629 b0e26479
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26479 b0e26629
        have b0e26693 : x = (M.op x (M.op x (σ y))) := by
          first
          | (have i₁ := b0e26677
             have i₂ := b0e26670
             grind)
          | exact superpose b0e26670 b0e26677
          | exact resolve b0e26677 b0e26670
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26670 b0e26677
        have b0e26705 : x = y := by
          first
          | (have i₁ := b0e26693
             have i₂ := b0e26435
             grind)
          | exact superpose b0e26435 b0e26693
          | exact resolve b0e26693 b0e26435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e26435 b0e26693
        have b0e28067 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b0e24
             have i₂ := b0e26705
             grind)
          | exact superpose b0e26705 b0e24
          | exact resolve b0e24 b0e26705
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e24 b0e26705
        have b0e28148 : False := by grind
        exact b0e28148
      · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b1e21 : y = (M.op y x) := by grind
          have b1e23 : x ≠ (M.op x y) := by grind
          have b1e24 : y = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e34 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b1e13 x y X0
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b1e13 x x X0
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 X0 x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e13
            | exact resolve b1e13 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e42 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b1e34 x
               have i₂ := b1e24
               grind)
            | exact superpose b1e24 b1e34
            | exact resolve b1e34 b1e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e71 : x = (M.op y x) := by
            first
            | (have i₁ := b1e34 y
               have i₂ := b1e42
               grind)
            | exact superpose b1e42 b1e34
            | exact resolve b1e34 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e34
          have b1e73 : ∀ X0 : G, (M.op y y) = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b1e13 (M.op y y) y X0
               have i₂ := b1e42
               grind)
            | exact superpose b1e42 b1e13
            | exact resolve b1e13 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e78 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 (M.op x (M.op X0 X0)) y X1
               have i₂ := b1e35 X0
               grind)
            | exact superpose b1e35 b1e13
            | exact resolve b1e13 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e80 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b1e78 X0 x
               have i₂ := b1e73 x
               grind)
            | exact superpose b1e73 b1e78
            | exact resolve b1e78 b1e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e73 b1e78
          have b1e82 : x = y := by
            first
            | (have i₁ := b1e21
               have i₂ := b1e71
               grind)
            | exact superpose b1e71 b1e21
            | exact resolve b1e21 b1e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e92 : x = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b1e38 y x
               have i₂ := b1e71
               grind)
            | exact superpose b1e71 b1e38
            | exact resolve b1e38 b1e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e71
          have b1e110 : x = (M.op y y) := by
            first
            | (have i₁ := b1e92
               have i₂ := b1e80 y
               grind)
            | exact superpose b1e80 b1e92
            | exact resolve b1e92 b1e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e80 b1e92
          have b1e120 : x = (M.op x x) := by
            first
            | (have i₁ := b1e110
               have i₂ := b1e82
               grind)
            | exact superpose b1e82 b1e110
            | exact resolve b1e110 b1e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e110
          have b1e130 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b1e23
               have i₂ := b1e82
               grind)
            | exact superpose b1e82 b1e23
            | exact resolve b1e23 b1e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e82
          have b1e143 : False := by grind
          exact b1e143
        · have b2e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b2e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b2e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b2e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b2e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b2e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b2e21 : y = (M.op y x) := by grind
          have b2e23 : x ≠ (M.op x y) := by grind
          have b2e24 : y ≠ (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : y ≠ y ∨ y = (k x y) := by
            first
            | (have i₁ := b2e16 x y
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e16
            | (have j0 := b2e16 x y
               grind)
            | (have r₁ := b2e16 x y
               have r₂ := b2e21
               grind)
            | exact resolve b2e16 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e29 : y = (k x y) := by grind
          clear b2e26
          have b2e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b2e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 (τ X0)
               have i₂ := b2e15 X0
               grind)
            | exact superpose b2e15 b2e19
            | exact resolve b2e19 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e14 (k (τ X0) X1)
               have i₂ := b2e31 X0 X1
               grind)
            | exact superpose b2e31 b2e14
            | exact resolve b2e14 b2e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e31
          have b2e37 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b2e13 x y X0
               have i₂ := b2e21
               grind)
            | exact superpose b2e21 b2e13
            | exact resolve b2e13 b2e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e39 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e13 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
               have i₂ := b2e13 X0 X1 X2
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
               have i₂ := b2e13 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b2e13 b2e13
            | exact resolve b2e13 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e44 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op y (M.op X1 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b2e13 (M.op y (M.op X0 X0)) y X1
               have i₂ := b2e37 X0
               grind)
            | exact superpose b2e37 b2e13
            | exact resolve b2e13 b2e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e37
          have b2e63 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e19 X1 X0
               have i₂ := b2e18 (σ X1) (σ X0)
               grind)
            | exact superpose b2e18 b2e19
            | (have j1 := b2e18 (σ X1) (σ X0)
               grind)
            | exact resolve b2e19 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e68 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b2e73 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b2e68 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e68
          have b2e76 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e73 X0 X1
               have j1 := b2e16 X0 X1
               grind)
            | (have r₁ := b2e73 X0 X1
               have r₂ := b2e16 X0 X1
               grind)
            | exact resolve b2e73 b2e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e73
          have b2e93 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e41 X0 X1 (M.op (M.op X1 X1) (M.op X2 X2))
               have i₂ := b2e13 X0 (M.op X1 X1) X2
               grind)
            | exact superpose b2e13 b2e41
            | exact resolve b2e41 b2e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e94 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e41 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b2e41 (M.op X0 X0) X0 X1
               grind)
            | exact superpose b2e41 b2e41
            | exact resolve b2e41 b2e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e41
          have b2e119 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e13 X1 X1 X2
               have i₂ := b2e94 X0 X1
               grind)
            | (have i₁ := b2e13 X1 X1 X2
               have i₂ := b2e94 X1 X0
               grind)
            | exact superpose b2e94 b2e13
            | exact resolve b2e13 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e123 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          have b2e130 : ∀ X0 : G, y ≠ (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b2e24
               have i₂ := b2e94 X0 x
               grind)
            | (have i₁ := b2e24
               have i₂ := b2e94 x X0
               grind)
            | exact superpose b2e94 b2e24
            | exact resolve b2e24 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b2e131 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b2e123 X0 X1
               have j1 := b2e16 (M.op X0 X0) X1
               grind)
            | (have r₁ := b2e123 X0 X1
               have r₂ := b2e16 (M.op X0 X0) X1
               grind)
            | exact resolve b2e123 b2e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e123
          have b2e143 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b2e76 (σ X0) (σ X1)
               have i₂ := b2e19 X0 X1
               grind)
            | exact superpose b2e19 b2e76
            | exact resolve b2e76 b2e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e76
          have b2e161 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e36 (M.op X1 X1) X0
               have i₂ := b2e131 X1 (σ X0)
               grind)
            | exact superpose b2e131 b2e36
            | exact resolve b2e36 b2e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e131
          have b2e164 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e161 X0 X1
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e161
            | exact resolve b2e161 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e161
          have b2e180 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (M.op X0 (M.op X3 X3))) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b2e39 X1 X1 X2 X3
               have i₂ := b2e18 X0 X1
               grind)
            | (have i₁ := b2e39 X0 X1 X2 X3
               have i₂ := b2e18 (M.op X1 X0) X1
               grind)
            | exact superpose b2e18 b2e39
            | (have j1 := b2e18 X0 X1
               grind)
            | exact resolve b2e39 b2e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e39
          have b2e259 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e36 (τ (M.op X1 X1)) X0
               have i₂ := b2e164 (σ X0) X1
               grind)
            | exact superpose b2e164 b2e36
            | exact resolve b2e36 b2e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e36 b2e164
          have b2e262 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b2e259 X0 X1
               have i₂ := b2e14 X0
               grind)
            | exact superpose b2e14 b2e259
            | exact resolve b2e259 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e259
          have b2e534 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) ∨ (σ X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b2e63 X0 X0
               have i₂ := b2e94 X0 (σ X0)
               grind)
            | (have i₁ := b2e63 X0 X0
               have i₂ := b2e94 (σ X0) X1
               grind)
            | exact superpose b2e94 b2e63
            | exact resolve b2e63 b2e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e63
          have b2e633 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have j0 := b2e534 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e534
          have b2e1055 : ∀ X0 X1 : G, y ≠ (M.op (M.op X0 X0) (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e130 x
               have i₂ := b2e93 x X0 X1
               grind)
            | (have i₁ := b2e130 (M.op x x)
               have i₂ := b2e93 X0 x x
               grind)
            | exact superpose b2e93 b2e130
            | exact resolve b2e130 b2e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e93 b2e130
          have b2e1660 : ∀ X0 X1 : G, y = (M.op (M.op X1 X1) (M.op x (M.op y (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e119 X1 y x
               have i₂ := b2e44 x X0
               grind)
            | exact superpose b2e44 b2e119
            | exact resolve b2e119 b2e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e44
          have b2e4120 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
            first
            | (have i₁ := b2e20
               have i₂ := b2e143 y x
               grind)
            | exact superpose b2e143 b2e20
            | (have j1 := b2e143 y x
               grind)
            | exact resolve b2e20 b2e143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e143
          have b2e13574 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b2e633 X1 (τ (τ (M.op X0 X0)))
               have i₂ := b2e262 (τ (τ (M.op X0 X0))) X0
               grind)
            | exact superpose b2e262 b2e633
            | (have j0 := b2e633 X1 (τ (τ (M.op X0 X0)))
               grind)
            | exact resolve b2e633 b2e262
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e262
          have b2e13807 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ (τ X1)) X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e32 X1 (τ X1)
               have i₂ := b2e633 X0 (τ X1)
               grind)
            | exact superpose b2e633 b2e32
            | (have j1 := b2e633 X0 (τ X1)
               grind)
            | exact resolve b2e32 b2e633
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e32 b2e633
          have b2e13841 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have j0 := b2e13574 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13574
          have b2e13861 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13807 X0 X1
               have i₂ := b2e15 X1
               grind)
            | exact superpose b2e15 b2e13807
            | (have j0 := b2e13807 X0 X1
               grind)
            | exact resolve b2e13807 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13807
          have b2e13921 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b2e13841 X0 X1
               have i₂ := b2e15 (τ (M.op X0 X0))
               grind)
            | exact superpose b2e15 b2e13841
            | exact resolve b2e13841 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13841
          have b2e13931 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b2e13861 X0 X1
               have i₂ := b2e15 X1
               grind)
            | exact superpose b2e15 b2e13861
            | (have j0 := b2e13861 X0 X1
               grind)
            | exact resolve b2e13861 b2e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13861
          have b2e15192 : ∀ X0 X1 : G, y ≠ (M.op (M.op X1 X1) (τ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b2e1055 X1 x
               have i₂ := b2e13921 X0 x
               grind)
            | exact superpose b2e13921 b2e1055
            | exact resolve b2e1055 b2e13921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e1055
          have b2e26937 : ∀ X0 X1 : G, y = (M.op (M.op X1 X1) (M.op x (M.op X0 X0))) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
            intro X0 X1
            first
            | (have i₁ := b2e1660 x X1
               have i₂ := b2e180 y x X0 x
               grind)
            | exact superpose b2e180 b2e1660
            | (have j1 := b2e180 y x x x
               grind)
            | exact resolve b2e1660 b2e180
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e180 b2e1660
          have b2e26971 : ∀ X0 X1 : G, y = (M.op (M.op X1 X1) (M.op x (M.op X0 X0))) ∨ (M.op x y) = (k y x) := by
            intro X0 X1
            first
            | (have j0 := b2e26937 X0 X1
               grind)
            | (have r₁ := b2e26937 X0 X1
               have r₂ := b2e23
               grind)
            | exact resolve b2e26937 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e26937
          have b2e27059 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have i₁ := b2e26971 x x
               have i₂ := b2e119 x x x
               grind)
            | exact superpose b2e119 b2e26971
            | exact resolve b2e26971 b2e119
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e119 b2e26971
          have b2e30837 : ∀ X0 X2 : G, y ≠ (M.op (τ (M.op X0 X0)) (τ (M.op X2 X2))) := by
            intro X0 X2
            first
            | (have i₁ := b2e15192 X2 x
               have i₂ := b2e13921 X0 x
               grind)
            | exact superpose b2e13921 b2e15192
            | exact resolve b2e15192 b2e13921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e13921 b2e15192
          have b2e83407 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (k X0 X0) ∨ (M.op X2 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b2e94 X2 X1
               have i₂ := b2e13931 X2 X0
               grind)
            | exact superpose b2e13931 b2e94
            | (have j1 := b2e13931 X1 X0
               grind)
            | exact resolve b2e94 b2e13931
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e94 b2e13931
          have b2e128563 : ∀ X0 X2 : G, y ≠ X0 ∨ (M.op X2 X2) = (k X0 X0) := by
            intro X0 X2
            first
            | (have i₁ := b2e30837 x x
               have i₂ := b2e83407 X0 X2 (τ (M.op x x))
               grind)
            | (have i₁ := b2e30837 X0 X2
               have i₂ := b2e83407 (M.op (τ (M.op X0 X0)) (τ (M.op X2 X2))) x X2
               grind)
            | exact superpose b2e83407 b2e30837
            | (have j1 := b2e83407 X0 X2 X2
               grind)
            | (have r₁ := b2e30837 X0 X0
               have r₂ := b2e83407 y x (τ (M.op X0 X0))
               grind)
            | exact resolve b2e30837 b2e83407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e83407
          have b2e129282 : ∀ X0 : G, (M.op X0 X0) = (k y y) := by
            intro X0
            first
            | (have j0 := b2e128563 y X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e128563
          have b2e130407 : y ≠ (k y y) := by
            first
            | (have i₁ := b2e30837 x x
               have i₂ := b2e129282 (τ (M.op x x))
               grind)
            | exact superpose b2e129282 b2e30837
            | exact resolve b2e30837 b2e129282
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e30837 b2e129282
          have b2e188784 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have i₁ := b2e4120
               have i₂ := b2e27059
               grind)
            | exact superpose b2e27059 b2e4120
            | exact resolve b2e4120 b2e27059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e4120 b2e27059
          have b2e188785 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
          clear b2e188784
          have b2e206051 : (M.op x y) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b2e14 (M.op x y)
               have i₂ := b2e188785
               grind)
            | exact superpose b2e188785 b2e14
            | exact resolve b2e14 b2e188785
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e188785
          have b2e206060 : x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b2e206051
               have i₂ := b2e14 x
               grind)
            | exact superpose b2e14 b2e206051
            | exact resolve b2e206051 b2e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e206051
          have b2e206061 : x = y := by
            first
            | (have r₁ := b2e206060
               have r₂ := b2e23
               grind)
            | exact resolve b2e206060 b2e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e206060
          have b2e206782 : x = (k x x) := by
            first
            | (have i₁ := b2e29
               have i₂ := b2e206061
               grind)
            | exact superpose b2e206061 b2e29
            | exact resolve b2e29 b2e206061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e29
          have b2e206889 : x ≠ (k x x) := by
            first
            | (have i₁ := b2e130407
               have i₂ := b2e206061
               grind)
            | exact superpose b2e206061 b2e130407
            | exact resolve b2e130407 b2e206061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b2e130407 b2e206061
          have b2e206974 : False := by grind
          exact b2e206974
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b3e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b3e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e23 : (σ x) = (M.op (σ y) (σ y)) := by grind
          have b3e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e20
            | exact resolve b3e20 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e37 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b3e13 y x X0
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e13
            | exact resolve b3e13 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (σ x))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b3e13 X1 X0 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e13
            | exact resolve b3e13 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
               have i₂ := b3e13 X0 (M.op X1 X1) X1
               grind)
            | exact superpose b3e13 b3e13
            | exact resolve b3e13 b3e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e44 : y = (M.op x (M.op x (σ x))) := by
            first
            | (have i₁ := b3e37 (σ y)
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e37
            | exact resolve b3e37 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b3e13 X1 X1 X2
               have i₂ := b3e18 X0 X1
               grind)
            | (have i₁ := b3e13 X0 X1 X2
               have i₂ := b3e18 (M.op X1 X0) X1
               grind)
            | exact superpose b3e18 b3e13
            | (have j1 := b3e18 X0 X1
               grind)
            | exact resolve b3e13 b3e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e105 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op x (σ x))) := by
            intro X0
            first
            | (have i₁ := b3e40 x (M.op x (M.op X0 X0))
               have i₂ := b3e37 X0
               grind)
            | exact superpose b3e37 b3e40
            | exact resolve b3e40 b3e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e106 : (M.op x (σ x)) = (M.op y (M.op x (σ x))) := by
            first
            | (have i₁ := b3e40 x (M.op x (σ x))
               have i₂ := b3e44
               grind)
            | exact superpose b3e44 b3e40
            | exact resolve b3e40 b3e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e40
          have b3e122 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (σ x)) := by
            intro X0
            first
            | (have i₁ := b3e105 X0
               have i₂ := b3e106
               grind)
            | exact superpose b3e106 b3e105
            | exact resolve b3e105 b3e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e105 b3e106
          have b3e134 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b3e41 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b3e41 (M.op X0 X0) X0 X1
               grind)
            | exact superpose b3e41 b3e41
            | exact resolve b3e41 b3e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e41
          have b3e176 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            grind
          have b3e189 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
            intro X0
            first
            | (have i₁ := b3e23
               have i₂ := b3e134 X0 (σ y)
               grind)
            | (have i₁ := b3e23
               have i₂ := b3e134 (σ y) X0
               grind)
            | exact superpose b3e134 b3e23
            | exact resolve b3e23 b3e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e134
          have b3e197 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b3e176 X0 X1
               have j1 := b3e16 (M.op X0 X0) X1
               grind)
            | (have r₁ := b3e176 X0 X1
               have r₂ := b3e16 (M.op X0 X0) X1
               grind)
            | exact resolve b3e176 b3e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e176
          have b3e211 : ∀ X1 : G, (k (σ x) X1) = X1 := by
            intro X1
            first
            | (have i₁ := b3e197 x X1
               have i₂ := b3e189 x
               grind)
            | exact superpose b3e189 b3e197
            | exact resolve b3e197 b3e189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e197
          have b3e252 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b3e19 x X0
               have i₂ := b3e211 (σ X0)
               grind)
            | exact superpose b3e211 b3e19
            | exact resolve b3e19 b3e211
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e211
          have b3e275 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b3e14 (k x X0)
               have i₂ := b3e252 X0
               grind)
            | exact superpose b3e252 b3e14
            | exact resolve b3e14 b3e252
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e252
          have b3e276 : ∀ X0 : G, (k x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b3e275 X0
               have i₂ := b3e14 X0
               grind)
            | exact superpose b3e14 b3e275
            | exact resolve b3e275 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e275
          have b3e708 : x = y ∨ (M.op x x) = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b3e37 x
               have i₂ := b3e63 x x x
               grind)
            | exact superpose b3e63 b3e37
            | (have j1 := b3e63 x x x
               grind)
            | exact resolve b3e37 b3e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e37 b3e63
          have b3e713 : x = (M.op x x) ∨ x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b3e708
               have i₂ := b3e276 x
               grind)
            | exact superpose b3e276 b3e708
            | exact resolve b3e708 b3e276
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e276 b3e708
          have b3e714 : x = (M.op x x) ∨ x = y := by grind
          clear b3e713
          have b3e763 : x = (σ x) ∨ x = y := by
            first
            | (have i₁ := b3e714
               have i₂ := b3e189 x
               grind)
            | exact superpose b3e189 b3e714
            | exact resolve b3e714 b3e189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e189 b3e714
          have b3e855 : y = (M.op x (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b3e44
               have i₂ := b3e763
               grind)
            | exact superpose b3e763 b3e44
            | exact resolve b3e44 b3e763
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e763
          have b3e867 : y = (M.op x (σ x)) ∨ x = y := by
            first
            | (have i₁ := b3e855
               have i₂ := b3e122 x
               grind)
            | exact superpose b3e122 b3e855
            | exact resolve b3e855 b3e122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e122 b3e855
          have b3e1572 : y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b3e44
               have i₂ := b3e867
               grind)
            | exact superpose b3e867 b3e44
            | exact resolve b3e44 b3e867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e44 b3e867
          have b3e1588 : x = y ∨ x = y := by
            first
            | (have i₁ := b3e1572
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e1572
            | exact resolve b3e1572 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1572
          have b3e1589 : x = y := by grind
          clear b3e1588
          have b3e1761 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b3e26
               have i₂ := b3e1589
               grind)
            | exact superpose b3e1589 b3e26
            | exact resolve b3e26 b3e1589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26
          have b3e1781 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b3e1761
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e1761
            | exact resolve b3e1761 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1761
          have b3e1787 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b3e1781
               have i₂ := b3e1589
               grind)
            | exact superpose b3e1589 b3e1781
            | exact resolve b3e1781 b3e1589
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1589 b3e1781
          have b3e1788 : False := by grind
          exact b3e1788
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b4e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e25 : x ≠ (M.op x y) := by grind
            have b4e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e39 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b4e14 x y X0
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e14
              | exact resolve b4e14 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e48 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b4e39 x
                 have i₂ := b4e26
                 grind)
              | exact superpose b4e26 b4e39
              | exact resolve b4e39 b4e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e84 : x = (M.op y x) := by
              first
              | (have i₁ := b4e39 y
                 have i₂ := b4e48
                 grind)
              | exact superpose b4e48 b4e39
              | exact resolve b4e39 b4e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e39 b4e48
            have b4e88 : x = y := by
              first
              | (have i₁ := b4e84
                 have i₂ := b4e22
                 grind)
              | exact superpose b4e22 b4e84
              | exact resolve b4e84 b4e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e84
            have b4e105 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b4e25
                 have i₂ := b4e88
                 grind)
              | exact superpose b4e88 b4e25
              | exact resolve b4e25 b4e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e106 : y = (M.op y y) := by
              first
              | (have i₁ := b4e26
                 have i₂ := b4e88
                 grind)
              | exact superpose b4e88 b4e26
              | exact resolve b4e26 b4e88
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e88
            have b4e113 : False := by grind
            exact b4e113
          · have b5e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b5e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b5e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b5e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b5e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b5e22 : y = (M.op y x) := by grind
            have b5e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
            have b5e25 : x ≠ (M.op x y) := by grind
            have b5e26 : y ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e34 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b5e14 x y X0
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e14
              | exact resolve b5e14 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e14 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
                 have i₂ := b5e14 X0 X1 X2
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e37 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (σ x))) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e14 X1 X0 (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e14
              | exact resolve b5e14 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e39 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b5e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b5e14 b5e14
              | exact resolve b5e14 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e41 : x = (M.op y (M.op y (σ x))) := by
              first
              | (have i₁ := b5e34 (σ y)
                 have i₂ := b5e24
                 grind)
              | exact superpose b5e24 b5e34
              | exact resolve b5e34 b5e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e43 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op y (M.op X1 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b5e14 (M.op y (M.op X0 X0)) y X1
                 have i₂ := b5e34 X0
                 grind)
              | exact superpose b5e34 b5e14
              | exact resolve b5e14 b5e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e50 : ∀ X0 : G, (M.op y (σ x)) = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b5e14 (M.op y (σ x)) y X0
                 have i₂ := b5e41
                 grind)
              | exact superpose b5e41 b5e14
              | exact resolve b5e14 b5e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e59 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 X1 X1 X2
                 have i₂ := b5e19 X0 X1
                 grind)
              | (have i₁ := b5e14 X0 X1 X2
                 have i₂ := b5e19 (M.op X1 X0) X1
                 grind)
              | exact superpose b5e19 b5e14
              | (have j1 := b5e19 X0 X1
                 grind)
              | exact resolve b5e14 b5e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e61 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b5e67 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b5e61 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e61
            have b5e70 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b5e67 X0 X1
                 have j1 := b5e17 X0 X1
                 grind)
              | (have r₁ := b5e67 X0 X1
                 have r₂ := b5e17 X0 X1
                 grind)
              | exact resolve b5e67 b5e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e67
            have b5e88 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e37 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                 have i₂ := b5e14 X0 X1 X2
                 grind)
              | exact superpose b5e14 b5e37
              | exact resolve b5e37 b5e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e89 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (M.op (M.op X1 X0) (σ x))) := by
              intro X0 X1
              first
              | (have i₁ := b5e37 (M.op X1 X0) (M.op X1 (σ x))
                 have i₂ := b5e37 X1 X0
                 grind)
              | exact superpose b5e37 b5e37
              | exact resolve b5e37 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e92 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op x (M.op y (σ x))) := by
              intro X0
              first
              | (have i₁ := b5e37 y (M.op y (M.op X0 X0))
                 have i₂ := b5e34 X0
                 grind)
              | exact superpose b5e34 b5e37
              | exact resolve b5e37 b5e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e34
            have b5e93 : (M.op y (σ x)) = (M.op x (M.op y (σ x))) := by
              first
              | (have i₁ := b5e37 y (M.op y (σ x))
                 have i₂ := b5e41
                 grind)
              | exact superpose b5e41 b5e37
              | exact resolve b5e37 b5e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e41
            have b5e101 : ∀ X0 X1 X2 : G, (M.op X1 (σ x)) = (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e14 (M.op X1 (σ x)) (M.op X1 X0) X2
                 have i₂ := b5e37 X1 X0
                 grind)
              | exact superpose b5e37 b5e14
              | exact resolve b5e14 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e104 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (σ x)) := by
              intro X0
              first
              | (have i₁ := b5e92 X0
                 have i₂ := b5e93
                 grind)
              | exact superpose b5e93 b5e92
              | exact resolve b5e92 b5e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e92 b5e93
            have b5e105 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 (σ x)) := by
              intro X1 X2
              first
              | (have i₁ := b5e88 x X1 X2
                 have i₂ := b5e89 x X1
                 grind)
              | exact superpose b5e89 b5e88
              | exact resolve b5e88 b5e89
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e88 b5e89
            have b5e115 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X1) (σ x)) := by
              intro X0 X1
              first
              | (have i₁ := b5e39 X0 X1 (M.op (M.op X1 X1) (σ x))
                 have i₂ := b5e37 (M.op X1 X1) X0
                 grind)
              | exact superpose b5e37 b5e39
              | exact resolve b5e39 b5e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e116 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
              intro X0 X1
              first
              | (have i₁ := b5e39 X1 (M.op X0 X0) (M.op X0 X0)
                 have i₂ := b5e39 (M.op X0 X0) X0 X1
                 grind)
              | exact superpose b5e39 b5e39
              | exact resolve b5e39 b5e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e39
            have b5e158 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              grind
            have b5e165 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) (M.op X0 X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b5e37 (σ x) X1
                 have i₂ := b5e116 X0 (σ x)
                 grind)
              | (have i₁ := b5e37 (σ x) X1
                 have i₂ := b5e116 (σ x) X0
                 grind)
              | exact superpose b5e116 b5e37
              | exact resolve b5e37 b5e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e37
            have b5e170 : ∀ X0 : G, (σ x) = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b5e24
                 have i₂ := b5e116 X0 (σ y)
                 grind)
              | (have i₁ := b5e24
                 have i₂ := b5e116 (σ y) X0
                 grind)
              | exact superpose b5e116 b5e24
              | exact resolve b5e24 b5e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e171 : ∀ X0 : G, y ≠ (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b5e26
                 have i₂ := b5e116 X0 x
                 grind)
              | (have i₁ := b5e26
                 have i₂ := b5e116 x X0
                 grind)
              | exact superpose b5e116 b5e26
              | exact resolve b5e26 b5e116
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e116
            have b5e174 : ∀ X1 : G, (M.op (M.op (σ x) X1) (σ x)) = X1 := by
              intro X1
              first
              | (have i₁ := b5e165 x X1
                 have i₂ := b5e105 (M.op (σ x) X1) x
                 grind)
              | exact superpose b5e105 b5e165
              | exact resolve b5e165 b5e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e165
            have b5e179 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b5e158 X0 X1
                 have j1 := b5e17 (M.op X0 X0) X1
                 grind)
              | (have r₁ := b5e158 X0 X1
                 have r₂ := b5e17 (M.op X0 X0) X1
                 grind)
              | exact resolve b5e158 b5e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e158
            have b5e193 : ∀ X1 : G, (k (σ x) X1) = X1 := by
              intro X1
              first
              | (have i₁ := b5e179 x X1
                 have i₂ := b5e170 x
                 grind)
              | exact superpose b5e170 b5e179
              | exact resolve b5e179 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e179
            have b5e215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b5e70 (σ X0) (σ X1)
                 have i₂ := b5e20 X0 X1
                 grind)
              | exact superpose b5e20 b5e70
              | exact resolve b5e70 b5e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e70
            have b5e445 : ∀ X0 : G, (σ X0) = (σ (k x X0)) := by
              intro X0
              first
              | (have i₁ := b5e20 x X0
                 have i₂ := b5e193 (σ X0)
                 grind)
              | exact superpose b5e193 b5e20
              | exact resolve b5e20 b5e193
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e193
            have b5e494 : ∀ X0 : G, (τ (σ X0)) = (k x X0) := by
              intro X0
              first
              | (have i₁ := b5e15 (k x X0)
                 have i₂ := b5e445 X0
                 grind)
              | exact superpose b5e445 b5e15
              | exact resolve b5e15 b5e445
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e445
            have b5e495 : ∀ X0 : G, (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b5e494 X0
                 have i₂ := b5e15 X0
                 grind)
              | exact superpose b5e15 b5e494
              | exact resolve b5e494 b5e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e494
            have b5e543 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op X0 X0) ∨ (M.op X0 x) = X0 := by
              intro X0
              first
              | (have i₁ := b5e19 x X0
                 have i₂ := b5e495 X0
                 grind)
              | exact superpose b5e495 b5e19
              | (have j0 := b5e19 x X0
                 grind)
              | exact resolve b5e19 b5e495
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e495
            have b5e545 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op X0 X0) := by
              intro X0
              first
              | (have j0 := b5e543 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e543
            have b5e548 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (σ x) := by
              intro X0
              first
              | (have i₁ := b5e545 X0
                 have i₂ := b5e170 X0
                 grind)
              | exact superpose b5e170 b5e545
              | (have j0 := b5e545 X0
                 grind)
              | exact resolve b5e545 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e545
            have b5e1503 : x = (σ x) ∨ x = (σ x) := by
              first
              | (have i₁ := b5e170 x
                 have i₂ := b5e548 x
                 grind)
              | exact superpose b5e548 b5e170
              | exact resolve b5e170 b5e548
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e548
            have b5e1520 : x = (σ x) := by grind
            clear b5e1503
            have b5e1687 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e21
              | exact resolve b5e21 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b5e1693 : ∀ X0 : G, (M.op (M.op x X0) x) = X0 := by
              intro X0
              first
              | (have i₁ := b5e174 x
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e174
              | exact resolve b5e174 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e174
            have b5e1945 : ∀ X0 X1 X2 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op y (σ x)) (M.op X2 X2))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b5e36 (M.op X1 X1) y X0 X2
                 have i₂ := b5e104 X1
                 grind)
              | exact superpose b5e104 b5e36
              | exact resolve b5e36 b5e104
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e104
            have b5e1953 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op y (σ x)) (σ x))) := by
              intro X0 X1
              first
              | (have i₁ := b5e1945 X0 X1 x
                 have i₂ := b5e105 (M.op y (σ x)) x
                 grind)
              | exact superpose b5e105 b5e1945
              | exact resolve b5e1945 b5e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1945
            have b5e1966 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op (M.op y x) x)) := by
              intro X0 X1
              first
              | (have i₁ := b5e1953 X0 X1
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e1953
              | exact resolve b5e1953 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1953
            have b5e1978 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X1 X1) (M.op y x)) := by
              intro X0 X1
              first
              | (have i₁ := b5e1966 X0 X1
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e1966
              | exact resolve b5e1966 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1966
            have b5e1989 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op (M.op X1 X1) y) := by
              intro X0 X1
              first
              | (have i₁ := b5e1978 X0 X1
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e1978
              | exact resolve b5e1978 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1978
            have b5e1995 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op (σ x) y) := by
              intro X0
              first
              | (have i₁ := b5e1989 X0 x
                 have i₂ := b5e170 x
                 grind)
              | exact superpose b5e170 b5e1989
              | exact resolve b5e1989 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1989
            have b5e2000 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b5e1995 X0
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e1995
              | exact resolve b5e1995 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1995
            have b5e2004 : (M.op x y) = (M.op y (σ x)) := by
              first
              | (have i₁ := b5e2000 x
                 have i₂ := b5e105 y x
                 grind)
              | exact superpose b5e105 b5e2000
              | exact resolve b5e2000 b5e105
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e105 b5e2000
            have b5e2005 : (M.op x y) = (M.op y x) := by
              first
              | (have i₁ := b5e2004
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e2004
              | exact resolve b5e2004 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2004
            have b5e2006 : y = (M.op x y) := by
              first
              | (have i₁ := b5e2005
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e2005
              | exact resolve b5e2005 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2005
            have b5e2293 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2))) (σ x)) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e115 X3 (M.op X1 X1)
                 have i₂ := b5e36 X0 (M.op X1 X1) X1 X2
                 grind)
              | exact superpose b5e36 b5e115
              | exact resolve b5e115 b5e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e36 b5e115
            have b5e2427 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op (M.op X0 (M.op (M.op (M.op X1 X1) X0) (M.op X2 X2))) x) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b5e2293 X0 X1 X2 X3
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e2293
              | exact resolve b5e2293 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2293
            have b5e2491 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) (σ x)) x) := by
              intro X1 X3
              first
              | (have i₁ := b5e2427 x X1 x X3
                 have i₂ := b5e101 x (M.op X1 X1) x
                 grind)
              | exact superpose b5e101 b5e2427
              | exact resolve b5e2427 b5e101
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e101 b5e2427
            have b5e2550 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op (M.op X1 X1) x) x) := by
              intro X1 X3
              first
              | (have i₁ := b5e2491 X1 X3
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e2491
              | exact resolve b5e2491 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2491
            have b5e2598 : ∀ X3 : G, (M.op X3 X3) = (M.op (M.op (σ x) x) x) := by
              intro X3
              first
              | (have i₁ := b5e2550 x X3
                 have i₂ := b5e170 x
                 grind)
              | exact superpose b5e170 b5e2550
              | exact resolve b5e2550 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2550
            have b5e2630 : ∀ X3 : G, (M.op X3 X3) = (M.op (M.op x x) x) := by
              intro X3
              first
              | (have i₁ := b5e2598 X3
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e2598
              | exact resolve b5e2598 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2598
            have b5e2649 : ∀ X3 : G, x = (M.op X3 X3) := by
              intro X3
              first
              | (have i₁ := b5e2630 X3
                 have i₂ := b5e1693 x
                 grind)
              | exact superpose b5e1693 b5e2630
              | exact resolve b5e2630 b5e1693
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1693 b5e2630
            have b5e3336 : (σ y) ≠ (M.op x (σ y)) := by
              first
              | (have i₁ := b5e1687
                 have i₂ := b5e2006
                 grind)
              | exact superpose b5e2006 b5e1687
              | exact resolve b5e1687 b5e2006
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1687
            have b5e3451 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op x (M.op y (M.op X0 X0))) ∨ (M.op (M.op X1 X1) y) = (k y (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X0 X1
              first
              | (have i₁ := b5e59 y (M.op X1 X1) X1
                 have i₂ := b5e43 (M.op X1 X1) X0
                 grind)
              | exact superpose b5e43 b5e59
              | (have j0 := b5e59 y (M.op X1 X1) x
                 grind)
              | exact resolve b5e59 b5e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e43 b5e59
            have b5e3486 : ∀ X1 : G, (M.op X1 X1) = (M.op y (σ x)) ∨ (M.op (M.op X1 X1) y) = (k y (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3451 x X1
                 have i₂ := b5e50 x
                 grind)
              | exact superpose b5e50 b5e3451
              | (have j0 := b5e3451 x X1
                 grind)
              | exact resolve b5e3451 b5e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e50 b5e3451
            have b5e3540 : ∀ X1 : G, (M.op X1 X1) = (M.op y x) ∨ (M.op (M.op X1 X1) y) = (k y (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3486 X1
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e3486
              | (have j0 := b5e3486 X1
                 grind)
              | exact resolve b5e3486 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3486
            have b5e3577 : ∀ X1 : G, (M.op X1 X1) = y ∨ (M.op (M.op X1 X1) y) = (k y (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3540 X1
                 have i₂ := b5e22
                 grind)
              | exact superpose b5e22 b5e3540
              | (have j0 := b5e3540 X1
                 grind)
              | exact resolve b5e3540 b5e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3540
            have b5e3610 : ∀ X1 : G, (M.op (M.op X1 X1) y) = (k y (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have j0 := b5e3577 X1
                 grind)
              | (have r₁ := b5e3577 x
                 have r₂ := b5e171 x
                 grind)
              | exact resolve b5e3577 b5e171
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e171 b5e3577
            have b5e3634 : ∀ X1 : G, (M.op (σ x) y) = (k y (σ x)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3610 x
                 have i₂ := b5e170 x
                 grind)
              | exact superpose b5e170 b5e3610
              | (have j0 := b5e3610 X1
                 grind)
              | exact resolve b5e3610 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3610
            have b5e3652 : ∀ X1 : G, (M.op x y) = (k y x) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3634 X1
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e3634
              | (have j0 := b5e3634 X1
                 grind)
              | exact resolve b5e3634 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3634
            have b5e3666 : ∀ X1 : G, y = (k y x) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) y) := by
              intro X1
              first
              | (have i₁ := b5e3652 X1
                 have i₂ := b5e2006
                 grind)
              | exact superpose b5e2006 b5e3652
              | (have j0 := b5e3652 X1
                 grind)
              | exact resolve b5e3652 b5e2006
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3652
            have b5e3677 : (σ x) = (M.op (σ x) y) ∨ y = (k y x) := by
              first
              | (have i₁ := b5e3666 x
                 have i₂ := b5e170 x
                 grind)
              | exact superpose b5e170 b5e3666
              | exact resolve b5e3666 b5e170
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e170 b5e3666
            have b5e3681 : x = (M.op x y) ∨ y = (k y x) := by
              first
              | (have i₁ := b5e3677
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e3677
              | exact resolve b5e3677 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3677
            have b5e3683 : y = (k y x) := by
              first
              | (have r₁ := b5e3681
                 have r₂ := b5e25
                 grind)
              | exact resolve b5e3681 b5e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3681
            have b5e8257 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b5e21
                 have i₂ := b5e215 y x
                 grind)
              | exact superpose b5e215 b5e21
              | (have j1 := b5e215 y x
                 grind)
              | exact resolve b5e21 b5e215
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e215
            have b5e8335 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b5e8257
                 have i₂ := b5e3683
                 grind)
              | exact superpose b5e3683 b5e8257
              | exact resolve b5e8257 b5e3683
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e8257
            have b5e8367 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b5e8335
                 have i₂ := b5e2006
                 grind)
              | exact superpose b5e2006 b5e8335
              | exact resolve b5e8335 b5e2006
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e2006 b5e8335
            have b5e8368 : (σ x) = (σ (k y x)) := by grind
            clear b5e8367
            have b5e8382 : (σ x) = (σ y) := by
              first
              | (have i₁ := b5e8368
                 have i₂ := b5e3683
                 grind)
              | exact superpose b5e3683 b5e8368
              | exact resolve b5e8368 b5e3683
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3683 b5e8368
            have b5e8387 : x = (σ y) := by
              first
              | (have i₁ := b5e8382
                 have i₂ := b5e1520
                 grind)
              | exact superpose b5e1520 b5e8382
              | exact resolve b5e8382 b5e1520
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e1520 b5e8382
            have b5e8399 : x ≠ (M.op x x) := by
              first
              | (have i₁ := b5e3336
                 have i₂ := b5e8387
                 grind)
              | exact superpose b5e8387 b5e3336
              | exact resolve b5e3336 b5e8387
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b5e3336 b5e8387
            have b5e8428 : False := by grind
            exact b5e8428
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b6e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b6e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b6e23 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e27 : y ≠ y ∨ y = (k x y) := by
            first
            | (have i₁ := b6e16 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e16
            | (have j0 := b6e16 x y
               grind)
            | (have r₁ := b6e16 x y
               have r₂ := b6e21
               grind)
            | exact resolve b6e16 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e30 : y = (k x y) := by grind
          clear b6e27
          have b6e63 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b6e23
               have i₂ := b6e18 X0 (σ y)
               grind)
            | (have i₁ := b6e23
               have i₂ := b6e18 (M.op (σ y) (σ y)) x
               grind)
            | exact superpose b6e18 b6e23
            | (have j1 := b6e18 X0 (σ y)
               grind)
            | (have r₁ := b6e23
               have r₂ := b6e18 (σ x) (σ y)
               grind)
            | exact resolve b6e23 b6e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e334 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b6e63 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e63
          have b6e335 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b6e334
               have r₂ := b6e22
               grind)
            | exact resolve b6e334 b6e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e334
          have b6e336 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b6e335
               have i₂ := b6e19 x y
               grind)
            | exact superpose b6e19 b6e335
            | exact resolve b6e335 b6e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e335
          have b6e337 : (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b6e336
               have i₂ := b6e30
               grind)
            | exact superpose b6e30 b6e336
            | exact resolve b6e336 b6e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e30 b6e336
          have b6e338 : False := by grind
          exact b6e338
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b7e22 : y = (M.op y x) := by grind
            have b7e25 : x ≠ (M.op x y) := by grind
            have b7e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e37 : ∀ X0 : G, x = (M.op y (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b7e14 x y X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e44 : x = (M.op y (M.op y y)) := by
              first
              | (have i₁ := b7e37 x
                 have i₂ := b7e26
                 grind)
              | exact superpose b7e26 b7e37
              | exact resolve b7e37 b7e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e75 : x = (M.op y x) := by
              first
              | (have i₁ := b7e37 y
                 have i₂ := b7e44
                 grind)
              | exact superpose b7e44 b7e37
              | exact resolve b7e37 b7e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37 b7e44
            have b7e79 : x = y := by
              first
              | (have i₁ := b7e75
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e75
              | exact resolve b7e75 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e75
            have b7e94 : y ≠ (M.op y y) := by
              first
              | (have i₁ := b7e25
                 have i₂ := b7e79
                 grind)
              | exact superpose b7e79 b7e25
              | exact resolve b7e25 b7e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e95 : y = (M.op y y) := by
              first
              | (have i₁ := b7e26
                 have i₂ := b7e79
                 grind)
              | exact superpose b7e79 b7e26
              | exact resolve b7e26 b7e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e79
            have b7e102 : False := by grind
            exact b7e102
          · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b8e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b8e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b8e22 : y = (M.op y x) := by grind
            have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : y ≠ y ∨ y = (k x y) := by
              first
              | (have i₁ := b8e17 x y
                 have i₂ := b8e22
                 grind)
              | exact superpose b8e22 b8e17
              | (have j0 := b8e17 x y
                 grind)
              | (have r₁ := b8e17 x y
                 have r₂ := b8e22
                 grind)
              | exact resolve b8e17 b8e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e29 : y = (k x y) := by grind
            clear b8e28
            have b8e60 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b8e24
                 have i₂ := b8e19 X0 (σ y)
                 grind)
              | (have i₁ := b8e24
                 have i₂ := b8e19 (M.op (σ y) (σ y)) x
                 grind)
              | exact superpose b8e19 b8e24
              | (have j1 := b8e19 X0 (σ y)
                 grind)
              | (have r₁ := b8e24
                 have r₂ := b8e19 (σ x) (σ y)
                 grind)
              | exact resolve b8e24 b8e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b8e285 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have j0 := b8e60 (σ x)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e60
            have b8e286 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b8e285
                 have r₂ := b8e23
                 grind)
              | exact resolve b8e285 b8e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e285
            have b8e287 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b8e286
                 have i₂ := b8e20 x y
                 grind)
              | exact superpose b8e20 b8e286
              | exact resolve b8e286 b8e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e286
            have b8e288 : (σ y) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b8e287
                 have i₂ := b8e29
                 grind)
              | exact superpose b8e29 b8e287
              | exact resolve b8e287 b8e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b8e29 b8e287
            have b8e289 : False := by grind
            exact b8e289
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b9e13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = (M.op y y) := by grind
          have b9e24 : x = (M.op x y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e41 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b9e13 y y X0
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e42 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b9e13 y x X0
               have i₂ := b9e24
               grind)
            | exact superpose b9e24 b9e13
            | exact resolve b9e13 b9e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e45 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b9e13 X1 X0 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e13
            | exact resolve b9e13 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e75 : y = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b9e41 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e41
            | exact resolve b9e41 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e80 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b9e42 y
               have i₂ := b9e22
               grind)
            | exact superpose b9e22 b9e42
            | exact resolve b9e42 b9e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b9e87 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b9e45 x (M.op y (M.op X0 X0))
               have i₂ := b9e41 X0
               grind)
            | exact superpose b9e41 b9e45
            | exact resolve b9e45 b9e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e41
          have b9e89 : (M.op y x) = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b9e45 x (M.op y x)
               have i₂ := b9e75
               grind)
            | exact superpose b9e75 b9e45
            | exact resolve b9e45 b9e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e75
          have b9e105 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b9e87 X0
               have i₂ := b9e89
               grind)
            | exact superpose b9e89 b9e87
            | exact resolve b9e87 b9e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e87 b9e89
          have b9e107 : y = (M.op x y) := by
            first
            | (have i₁ := b9e42 x
               have i₂ := b9e80
               grind)
            | exact superpose b9e80 b9e42
            | exact resolve b9e42 b9e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e42 b9e80
          have b9e121 : y = (M.op y (M.op x x)) := by
            first
            | (have i₁ := b9e45 x y
               have i₂ := b9e107
               grind)
            | exact superpose b9e107 b9e45
            | exact resolve b9e45 b9e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e45 b9e107
          have b9e125 : y = (M.op y x) := by
            first
            | (have i₁ := b9e121
               have i₂ := b9e105 x
               grind)
            | exact superpose b9e105 b9e121
            | exact resolve b9e121 b9e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b9e105 b9e121
          have b9e127 : False := by grind
          exact b9e127
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b10e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b10e23 : x = (M.op y y) := by grind
            have b10e25 : x ≠ (M.op x y) := by grind
            have b10e26 : y = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e43 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b10e14 x x X0
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e14
              | exact resolve b10e14 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e44 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b10e14 y y X0
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e47 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b10e14 X1 X0 y
                 have i₂ := b10e23
                 grind)
              | exact superpose b10e23 b10e14
              | exact resolve b10e14 b10e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e78 : x = (M.op y (M.op x y)) := by
              first
              | (have i₁ := b10e43 x
                 have i₂ := b10e26
                 grind)
              | exact superpose b10e26 b10e43
              | exact resolve b10e43 b10e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e88 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x (M.op X1 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b10e14 (M.op y (M.op X0 X0)) x X1
                 have i₂ := b10e44 X0
                 grind)
              | exact superpose b10e44 b10e14
              | exact resolve b10e14 b10e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e90 : ∀ X0 : G, x = (M.op y (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b10e88 X0 x
                 have i₂ := b10e43 x
                 grind)
              | exact superpose b10e43 b10e88
              | exact resolve b10e88 b10e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e43 b10e88
            have b10e91 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b10e14 (M.op x y) y X0
                 have i₂ := b10e78
                 grind)
              | exact superpose b10e78 b10e14
              | exact resolve b10e14 b10e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e78
            have b10e93 : y = (M.op x y) := by
              first
              | (have i₁ := b10e91 x
                 have i₂ := b10e44 x
                 grind)
              | exact superpose b10e44 b10e91
              | exact resolve b10e91 b10e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e44 b10e91
            have b10e119 : x ≠ y := by
              first
              | (have i₁ := b10e25
                 have i₂ := b10e93
                 grind)
              | exact superpose b10e93 b10e25
              | exact resolve b10e25 b10e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e132 : y = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b10e47 x y
                 have i₂ := b10e93
                 grind)
              | exact superpose b10e93 b10e47
              | exact resolve b10e47 b10e93
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e47 b10e93
            have b10e152 : x = y := by
              first
              | (have i₁ := b10e132
                 have i₂ := b10e90 x
                 grind)
              | exact superpose b10e90 b10e132
              | exact resolve b10e132 b10e90
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e90 b10e132
            have b10e156 : False := by grind
            exact b10e156
          · have b11e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b11e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b11e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b11e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b11e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b11e23 : x = (M.op y y) := by grind
            have b11e25 : x ≠ (M.op x y) := by grind
            have b11e26 : y ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e34 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 (τ X0) X1
                 have i₂ := b11e16 X0
                 grind)
              | exact superpose b11e16 b11e20
              | exact resolve b11e20 b11e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e40 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b11e14 y y X0
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X1 X0 y
                 have i₂ := b11e23
                 grind)
              | exact superpose b11e23 b11e14
              | exact resolve b11e14 b11e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e45 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b11e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b11e14 b11e14
              | exact resolve b11e14 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e60 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b11e20 X1 X0
                 have i₂ := b11e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b11e19 b11e20
              | (have j1 := b11e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b11e20 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e63 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e14 X1 X1 X2
                 have i₂ := b11e19 X0 X1
                 grind)
              | (have i₁ := b11e14 X0 X1 X2
                 have i₂ := b11e19 (M.op X1 X0) X1
                 grind)
              | exact superpose b11e19 b11e14
              | (have j1 := b11e19 X0 X1
                 grind)
              | exact resolve b11e14 b11e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e65 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b11e70 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              first
              | (have j0 := b11e65 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e65
            have b11e73 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b11e70 X0 X1
                 have j1 := b11e17 X0 X1
                 grind)
              | (have r₁ := b11e70 X0 X1
                 have r₂ := b11e17 X0 X1
                 grind)
              | exact resolve b11e70 b11e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e70
            have b11e75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) x)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b11e43 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                 have i₂ := b11e14 X0 X1 X2
                 grind)
              | exact superpose b11e14 b11e43
              | exact resolve b11e43 b11e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e76 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) x)) := by
              intro X0 X1
              first
              | (have i₁ := b11e43 (M.op X1 X0) (M.op X1 x)
                 have i₂ := b11e43 X1 X0
                 grind)
              | exact superpose b11e43 b11e43
              | exact resolve b11e43 b11e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e82 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b11e14 X1 (M.op x X0) x
                 have i₂ := b11e43 x X0
                 grind)
              | exact superpose b11e43 b11e14
              | exact resolve b11e14 b11e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e91 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
              intro X1 X2
              first
              | (have i₁ := b11e75 x X1 X2
                 have i₂ := b11e76 x X1
                 grind)
              | exact superpose b11e76 b11e75
              | exact resolve b11e75 b11e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e75 b11e76
            have b11e96 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b11e15 (k (τ X0) X1)
                 have i₂ := b11e34 X0 X1
                 grind)
              | exact superpose b11e34 b11e15
              | exact resolve b11e15 b11e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e34
            have b11e100 : ∀ X0 : G, (M.op x x) = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b11e82 X0 (M.op x x)
                 have i₂ := b11e43 x X0
                 grind)
              | exact superpose b11e43 b11e82
              | exact resolve b11e82 b11e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e139 : ∀ X0 : G, (k (M.op x x) X0) = X0 ∨ (M.op X0 (M.op x x)) = X0 := by
              intro X0
              grind
            have b11e147 : x = (M.op x x) := by
              first
              | (have i₁ := b11e43 x x
                 have i₂ := b11e100 (M.op x x)
                 grind)
              | exact superpose b11e100 b11e43
              | exact resolve b11e43 b11e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e43
            have b11e153 : ∀ X0 : G, (k (M.op x x) X0) = X0 := by
              intro X0
              first
              | (have j0 := b11e139 X0
                 have j1 := b11e17 (M.op x x) X0
                 grind)
              | (have r₁ := b11e139 x
                 have r₂ := b11e17 (M.op x x) x
                 grind)
              | exact resolve b11e139 b11e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e139
            have b11e161 : ∀ X0 : G, (k x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b11e153 X0
                 have i₂ := b11e147
                 grind)
              | exact superpose b11e147 b11e153
              | exact resolve b11e153 b11e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e153
            have b11e177 : ∀ X0 : G, x = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b11e45 X0 x x
                 have i₂ := b11e82 x X0
                 grind)
              | exact superpose b11e82 b11e45
              | exact resolve b11e45 b11e82
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e45 b11e82
            have b11e236 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b11e73 (σ X0) (σ X1)
                 have i₂ := b11e20 X0 X1
                 grind)
              | exact superpose b11e20 b11e73
              | exact resolve b11e73 b11e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e73
            have b11e666 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b11e40 (M.op X0 X0)
                 have i₂ := b11e63 y (M.op X0 X0) X0
                 grind)
              | exact superpose b11e63 b11e40
              | (have j1 := b11e63 y (M.op X0 X0) x
                 grind)
              | exact resolve b11e40 b11e63
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e40 b11e63
            have b11e667 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b11e666 X0
                 have i₂ := b11e91 x X0
                 grind)
              | exact superpose b11e91 b11e666
              | (have j0 := b11e666 X0
                 grind)
              | exact resolve b11e666 b11e91
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e91 b11e666
            have b11e713 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have j0 := b11e667 X0
                 grind)
              | (have r₁ := b11e667 X0
                 have r₂ := b11e26
                 grind)
              | exact resolve b11e667 b11e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e667
            have b11e752 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
              intro X0
              first
              | (have i₁ := b11e713 X0
                 have i₂ := b11e177 X0
                 grind)
              | exact superpose b11e177 b11e713
              | (have j0 := b11e713 X0
                 grind)
              | exact resolve b11e713 b11e177
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e713
            have b11e779 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
              first
              | (have i₁ := b11e752 x
                 have i₂ := b11e177 x
                 grind)
              | exact superpose b11e177 b11e752
              | exact resolve b11e752 b11e177
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e177 b11e752
            have b11e796 : (M.op x y) = (k y x) := by
              first
              | (have r₁ := b11e779
                 have r₂ := b11e25
                 grind)
              | exact resolve b11e779 b11e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e779
            have b11e1200 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b11e60 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e60
            have b11e1202 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b11e1200 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e1200
            have b11e1227 : ∀ X0 : G, (σ X0) = (M.op x x) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
              intro X0
              first
              | (have i₁ := b11e1202 X0
                 have i₂ := b11e100 (σ X0)
                 grind)
              | exact superpose b11e100 b11e1202
              | (have j0 := b11e1202 X0
                 grind)
              | exact resolve b11e1202 b11e100
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e100 b11e1202
            have b11e1291 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = x := by
              intro X0
              first
              | (have i₁ := b11e1227 X0
                 have i₂ := b11e147
                 grind)
              | exact superpose b11e147 b11e1227
              | (have j0 := b11e1227 X0
                 grind)
              | exact resolve b11e1227 b11e147
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e147 b11e1227
            have b11e2265 : ∀ X0 : G, (τ (σ X0)) = (k (τ x) X0) := by
              intro X0
              first
              | (have i₁ := b11e96 x X0
                 have i₂ := b11e161 (σ X0)
                 grind)
              | exact superpose b11e161 b11e96
              | exact resolve b11e96 b11e161
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e2269 : ∀ X0 : G, (k (τ x) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b11e2265 X0
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e2265
              | exact resolve b11e2265 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2265
            have b11e2297 : ∀ X0 : G, (τ (σ X0)) = (k (τ (τ x)) X0) := by
              intro X0
              first
              | (have i₁ := b11e96 (τ x) X0
                 have i₂ := b11e2269 (σ X0)
                 grind)
              | exact superpose b11e2269 b11e96
              | exact resolve b11e96 b11e2269
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e96 b11e2269
            have b11e2310 : ∀ X0 : G, (k (τ (τ x)) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b11e2297 X0
                 have i₂ := b11e15 X0
                 grind)
              | exact superpose b11e15 b11e2297
              | exact resolve b11e2297 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2297
            have b11e2520 : (σ (τ (τ x))) ≠ (σ (τ (τ x))) ∨ x = (σ (τ (τ x))) := by
              first
              | (have i₁ := b11e1291 (τ (τ x))
                 have i₂ := b11e2310 (τ (τ x))
                 grind)
              | exact superpose b11e2310 b11e1291
              | (have j0 := b11e1291 (τ (τ x))
                 grind)
              | exact resolve b11e1291 b11e2310
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2310
            have b11e2522 : (σ x) ≠ (σ x) ∨ x = (σ x) := by
              first
              | (have i₁ := b11e1291 x
                 have i₂ := b11e161 x
                 grind)
              | exact superpose b11e161 b11e1291
              | (have j0 := b11e1291 x
                 grind)
              | exact resolve b11e1291 b11e161
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e161 b11e1291
            have b11e2526 : x = (σ x) := by grind
            clear b11e2522
            have b11e2528 : x = (σ (τ (τ x))) := by grind
            clear b11e2520
            have b11e2538 : x = (τ x) := by
              first
              | (have i₁ := b11e2528
                 have i₂ := b11e16 (τ x)
                 grind)
              | exact superpose b11e16 b11e2528
              | exact resolve b11e2528 b11e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2528
            have b11e5837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b11e21
                 have i₂ := b11e236 y x
                 grind)
              | exact superpose b11e236 b11e21
              | (have j1 := b11e236 y x
                 grind)
              | exact resolve b11e21 b11e236
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e236
            have b11e5900 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k y x)) := by
              first
              | (have i₁ := b11e5837
                 have i₂ := b11e796
                 grind)
              | exact superpose b11e796 b11e5837
              | exact resolve b11e5837 b11e796
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e5837
            have b11e5901 : (σ x) = (σ (k y x)) := by grind
            clear b11e5900
            have b11e5915 : (σ (M.op x y)) = (σ x) := by
              first
              | (have i₁ := b11e5901
                 have i₂ := b11e796
                 grind)
              | exact superpose b11e796 b11e5901
              | exact resolve b11e5901 b11e796
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e796 b11e5901
            have b11e5921 : x = (σ (M.op x y)) := by
              first
              | (have i₁ := b11e5915
                 have i₂ := b11e2526
                 grind)
              | exact superpose b11e2526 b11e5915
              | exact resolve b11e5915 b11e2526
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2526 b11e5915
            have b11e5925 : (M.op x y) = (τ x) := by
              first
              | (have i₁ := b11e15 (M.op x y)
                 have i₂ := b11e5921
                 grind)
              | exact superpose b11e5921 b11e15
              | exact resolve b11e15 b11e5921
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e5921
            have b11e5955 : x = (M.op x y) := by
              first
              | (have i₁ := b11e5925
                 have i₂ := b11e2538
                 grind)
              | exact superpose b11e2538 b11e5925
              | exact resolve b11e5925 b11e2538
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e2538 b11e5925
            have b11e5959 : False := by grind
            exact b11e5959
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b12e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b12e22 : y ≠ (M.op y x) := by grind
            have b12e23 : x = (M.op y y) := by grind
            have b12e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e36 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b12e14 y y X0
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e37 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b12e14 y x X0
                 have i₂ := b12e26
                 grind)
              | exact superpose b12e26 b12e14
              | exact resolve b12e14 b12e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e40 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b12e14 X1 X0 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e14
              | exact resolve b12e14 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e77 : y = (M.op x (M.op y x)) := by
              first
              | (have i₁ := b12e36 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e36
              | exact resolve b12e36 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e83 : y = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b12e37 y
                 have i₂ := b12e23
                 grind)
              | exact superpose b12e23 b12e37
              | exact resolve b12e37 b12e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b12e90 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b12e40 x (M.op y (M.op X0 X0))
                 have i₂ := b12e36 X0
                 grind)
              | exact superpose b12e36 b12e40
              | exact resolve b12e40 b12e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e36
            have b12e92 : (M.op y x) = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b12e40 x (M.op y x)
                 have i₂ := b12e77
                 grind)
              | exact superpose b12e77 b12e40
              | exact resolve b12e40 b12e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e77
            have b12e108 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b12e90 X0
                 have i₂ := b12e92
                 grind)
              | exact superpose b12e92 b12e90
              | exact resolve b12e90 b12e92
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e90 b12e92
            have b12e110 : y = (M.op x y) := by
              first
              | (have i₁ := b12e37 x
                 have i₂ := b12e83
                 grind)
              | exact superpose b12e83 b12e37
              | exact resolve b12e37 b12e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e37 b12e83
            have b12e124 : y = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b12e40 x y
                 have i₂ := b12e110
                 grind)
              | exact superpose b12e110 b12e40
              | exact resolve b12e40 b12e110
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e40 b12e110
            have b12e128 : y = (M.op y x) := by
              first
              | (have i₁ := b12e124
                 have i₂ := b12e108 x
                 grind)
              | exact superpose b12e108 b12e124
              | exact resolve b12e124 b12e108
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b12e108 b12e124
            have b12e130 : False := by grind
            exact b12e130
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b13e24 : x = (M.op y y) := by grind
              have b13e27 : x ≠ (M.op x y) := by grind
              have b13e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e38 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b13e15 x x X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e39 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b13e15 y y X0
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e43 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X1 X0 y
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e48 : x = (M.op y (M.op x y)) := by
                first
                | (have i₁ := b13e38 x
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e38
                | exact resolve b13e38 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e91 : ∀ X0 X1 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x (M.op X1 X1))) := by
                intro X0 X1
                first
                | (have i₁ := b13e15 (M.op y (M.op X0 X0)) x X1
                   have i₂ := b13e39 X0
                   grind)
                | exact superpose b13e39 b13e15
                | exact resolve b13e15 b13e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e93 : ∀ X0 : G, x = (M.op y (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b13e91 X0 x
                   have i₂ := b13e38 x
                   grind)
                | exact superpose b13e38 b13e91
                | exact resolve b13e91 b13e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e38 b13e91
              have b13e94 : ∀ X0 : G, (M.op x y) = (M.op x (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b13e15 (M.op x y) y X0
                   have i₂ := b13e48
                   grind)
                | exact superpose b13e48 b13e15
                | exact resolve b13e15 b13e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e48
              have b13e96 : y = (M.op x y) := by
                first
                | (have i₁ := b13e94 x
                   have i₂ := b13e39 x
                   grind)
                | exact superpose b13e39 b13e94
                | exact resolve b13e94 b13e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e39 b13e94
              have b13e122 : x ≠ y := by
                first
                | (have i₁ := b13e27
                   have i₂ := b13e96
                   grind)
                | exact superpose b13e96 b13e27
                | exact resolve b13e27 b13e96
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e135 : y = (M.op y (M.op x x)) := by
                first
                | (have i₁ := b13e43 x y
                   have i₂ := b13e96
                   grind)
                | exact superpose b13e96 b13e43
                | exact resolve b13e43 b13e96
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e43 b13e96
              have b13e155 : x = y := by
                first
                | (have i₁ := b13e135
                   have i₂ := b13e93 x
                   grind)
                | exact superpose b13e93 b13e135
                | exact resolve b13e135 b13e93
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e93 b13e135
              have b13e159 : False := by grind
              exact b13e159
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b14e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b14e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : x = (M.op y y) := by grind
              have b14e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              have b14e27 : x ≠ (M.op x y) := by grind
              have b14e28 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e39 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e15 y y X0
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 X0 y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e45 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                   have i₂ := b14e15 X0 (M.op X1 X1) X1
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e48 : y = (M.op x (M.op y (σ x))) := by
                first
                | (have i₁ := b14e39 (σ y)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e39
                | exact resolve b14e39 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e49 : y = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b14e39 y
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e39
                | exact resolve b14e39 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e67 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X2))) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X1 X1 X2
                   have i₂ := b14e20 X0 X1
                   grind)
                | (have i₁ := b14e15 X0 X1 X2
                   have i₂ := b14e20 (M.op X1 X0) X1
                   grind)
                | exact superpose b14e20 b14e15
                | (have j1 := b14e20 X0 X1
                   grind)
                | exact resolve b14e15 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e69 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b14e75 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b14e69 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e69
              have b14e78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b14e75 X0 X1
                   have j1 := b14e18 X0 X1
                   grind)
                | (have r₁ := b14e75 X0 X1
                   have r₂ := b14e18 X0 X1
                   grind)
                | exact resolve b14e75 b14e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e75
              have b14e79 : ∀ X0 : G, (M.op y x) = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e15 (M.op y x) x X0
                   have i₂ := b14e49
                   grind)
                | exact superpose b14e49 b14e15
                | exact resolve b14e15 b14e49
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e49
              have b14e82 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) x)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e42 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                   have i₂ := b14e15 X0 X1 X2
                   grind)
                | exact superpose b14e15 b14e42
                | exact resolve b14e42 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e83 : ∀ X0 X1 : G, (M.op X1 x) = (M.op X0 (M.op (M.op X1 X0) x)) := by
                intro X0 X1
                first
                | (have i₁ := b14e42 (M.op X1 X0) (M.op X1 x)
                   have i₂ := b14e42 X1 X0
                   grind)
                | exact superpose b14e42 b14e42
                | exact resolve b14e42 b14e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e42
              have b14e98 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 x) := by
                intro X1 X2
                first
                | (have i₁ := b14e82 x X1 X2
                   have i₂ := b14e83 x X1
                   grind)
                | exact superpose b14e83 b14e82
                | exact resolve b14e82 b14e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e82 b14e83
              have b14e100 : ∀ X0 : G, (M.op y (σ x)) = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e15 (M.op y (σ x)) x X0
                   have i₂ := b14e48
                   grind)
                | exact superpose b14e48 b14e15
                | exact resolve b14e15 b14e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e48
              have b14e102 : (M.op y x) = (M.op y (σ x)) := by
                first
                | (have i₁ := b14e100 x
                   have i₂ := b14e79 x
                   grind)
                | exact superpose b14e79 b14e100
                | exact resolve b14e100 b14e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e79 b14e100
              have b14e118 : ∀ X0 : G, (σ x) = (M.op (M.op y x) (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b14e15 (σ x) y X0
                   have i₂ := b14e102
                   grind)
                | exact superpose b14e102 b14e15
                | exact resolve b14e15 b14e102
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e102
              have b14e120 : x = (σ x) := by
                first
                | (have i₁ := b14e118 x
                   have i₂ := b14e15 x y x
                   grind)
                | exact superpose b14e15 b14e118
                | exact resolve b14e118 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e118
              have b14e175 : x = (τ x) := by
                first
                | (have i₁ := b14e16 x
                   have i₂ := b14e120
                   grind)
                | exact superpose b14e120 b14e16
                | exact resolve b14e16 b14e120
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e190 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e45 X1 (M.op X0 X0) (M.op X0 X0)
                   have i₂ := b14e45 (M.op X0 X0) X0 X1
                   grind)
                | exact superpose b14e45 b14e45
                | exact resolve b14e45 b14e45
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e45
              have b14e269 : ∀ X0 : G, x = (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b14e24
                   have i₂ := b14e190 X0 y
                   grind)
                | (have i₁ := b14e24
                   have i₂ := b14e190 y X0
                   grind)
                | exact superpose b14e190 b14e24
                | exact resolve b14e24 b14e190
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e190
              have b14e338 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e78 (σ X0) (σ X1)
                   have i₂ := b14e21 X0 X1
                   grind)
                | exact superpose b14e21 b14e78
                | exact resolve b14e78 b14e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e78
              have b14e821 : ∀ X0 : G, y = (M.op x (M.op X0 X0)) ∨ (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b14e39 (M.op X0 X0)
                   have i₂ := b14e67 y (M.op X0 X0) X0
                   grind)
                | exact superpose b14e67 b14e39
                | (have j1 := b14e67 y (M.op X0 X0) x
                   grind)
                | exact resolve b14e39 b14e67
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e39 b14e67
              have b14e822 : ∀ X0 : G, y = (M.op x x) ∨ (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b14e821 X0
                   have i₂ := b14e98 x X0
                   grind)
                | exact superpose b14e98 b14e821
                | (have j0 := b14e821 X0
                   grind)
                | exact resolve b14e821 b14e98
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e98 b14e821
              have b14e868 : ∀ X0 : G, (M.op (M.op X0 X0) y) = (k y (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have j0 := b14e822 X0
                   grind)
                | (have r₁ := b14e822 X0
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e822 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e822
              have b14e906 : ∀ X0 : G, (M.op x y) = (k y x) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b14e868 X0
                   have i₂ := b14e269 X0
                   grind)
                | exact superpose b14e269 b14e868
                | (have j0 := b14e868 X0
                   grind)
                | exact resolve b14e868 b14e269
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e868
              have b14e932 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by
                first
                | (have i₁ := b14e906 x
                   have i₂ := b14e269 x
                   grind)
                | exact superpose b14e269 b14e906
                | exact resolve b14e906 b14e269
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e269 b14e906
              have b14e945 : (M.op x y) = (k y x) := by
                first
                | (have r₁ := b14e932
                   have r₂ := b14e27
                   grind)
                | exact resolve b14e932 b14e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e932
              have b14e6618 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e338 y x
                   grind)
                | exact superpose b14e338 b14e22
                | (have j1 := b14e338 y x
                   grind)
                | exact resolve b14e22 b14e338
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e338
              have b14e6677 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b14e6618
                   have i₂ := b14e945
                   grind)
                | exact superpose b14e945 b14e6618
                | exact resolve b14e6618 b14e945
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6618
              have b14e6678 : (σ x) = (σ (k y x)) := by grind
              clear b14e6677
              have b14e6691 : (σ (M.op x y)) = (σ x) := by
                first
                | (have i₁ := b14e6678
                   have i₂ := b14e945
                   grind)
                | exact superpose b14e945 b14e6678
                | exact resolve b14e6678 b14e945
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e945 b14e6678
              have b14e6696 : x = (σ (M.op x y)) := by
                first
                | (have i₁ := b14e6691
                   have i₂ := b14e120
                   grind)
                | exact superpose b14e120 b14e6691
                | exact resolve b14e6691 b14e120
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e120 b14e6691
              have b14e6698 : (M.op x y) = (τ x) := by
                first
                | (have i₁ := b14e16 (M.op x y)
                   have i₂ := b14e6696
                   grind)
                | exact superpose b14e6696 b14e16
                | exact resolve b14e16 b14e6696
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e6696
              have b14e6730 : x = (M.op x y) := by
                first
                | (have i₁ := b14e6698
                   have i₂ := b14e175
                   grind)
                | exact superpose b14e175 b14e6698
                | exact resolve b14e6698 b14e175
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e175 b14e6698
              have b14e6735 : False := by grind
              exact b14e6735
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b15e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b15e22 : y ≠ (M.op y x) := by grind
            have b15e23 : x = (M.op y y) := by grind
            have b15e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e34 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b15e14 y y X0
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e35 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b15e14 y x X0
                 have i₂ := b15e26
                 grind)
              | exact superpose b15e26 b15e14
              | exact resolve b15e14 b15e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e37 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b15e14 X1 X0 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e14
              | exact resolve b15e14 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e66 : y = (M.op x (M.op y x)) := by
              first
              | (have i₁ := b15e34 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e34
              | exact resolve b15e34 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e71 : y = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b15e35 y
                 have i₂ := b15e23
                 grind)
              | exact superpose b15e23 b15e35
              | exact resolve b15e35 b15e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b15e81 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (M.op y (M.op x x)) := by
              intro X0
              first
              | (have i₁ := b15e37 x (M.op y (M.op X0 X0))
                 have i₂ := b15e34 X0
                 grind)
              | exact superpose b15e34 b15e37
              | exact resolve b15e37 b15e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e34
            have b15e83 : (M.op y x) = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b15e37 x (M.op y x)
                 have i₂ := b15e66
                 grind)
              | exact superpose b15e66 b15e37
              | exact resolve b15e37 b15e66
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e66
            have b15e97 : ∀ X0 : G, (M.op y x) = (M.op y (M.op X0 X0)) := by
              intro X0
              first
              | (have i₁ := b15e81 X0
                 have i₂ := b15e83
                 grind)
              | exact superpose b15e83 b15e81
              | exact resolve b15e81 b15e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e81 b15e83
            have b15e99 : y = (M.op x y) := by
              first
              | (have i₁ := b15e35 x
                 have i₂ := b15e71
                 grind)
              | exact superpose b15e71 b15e35
              | exact resolve b15e35 b15e71
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e35 b15e71
            have b15e113 : y = (M.op y (M.op x x)) := by
              first
              | (have i₁ := b15e37 x y
                 have i₂ := b15e99
                 grind)
              | exact superpose b15e99 b15e37
              | exact resolve b15e37 b15e99
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e37 b15e99
            have b15e117 : y = (M.op y x) := by
              first
              | (have i₁ := b15e113
                 have i₂ := b15e97 x
                 grind)
              | exact superpose b15e97 b15e113
              | exact resolve b15e113 b15e97
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b15e97 b15e113
            have b15e119 : False := by grind
            exact b15e119
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b16e23 : y ≠ (M.op y x) := by grind
              have b16e24 : x = (M.op y y) := by grind
              have b16e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e34 : ∀ X0 : G, y = (M.op x (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b16e15 y y X0
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e35 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b16e15 x x X0
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e42 : y = (M.op x (M.op y x)) := by
                first
                | (have i₁ := b16e34 y
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e34
                | exact resolve b16e34 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e84 : ∀ X0 : G, (M.op y x) = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b16e15 (M.op y x) x X0
                   have i₂ := b16e42
                   grind)
                | exact superpose b16e42 b16e15
                | exact resolve b16e15 b16e42
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e42
              have b16e86 : x = (M.op y x) := by
                first
                | (have i₁ := b16e84 x
                   have i₂ := b16e35 x
                   grind)
                | exact superpose b16e35 b16e84
                | exact resolve b16e84 b16e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e35 b16e84
              have b16e111 : x ≠ y := by
                first
                | (have i₁ := b16e23
                   have i₂ := b16e86
                   grind)
                | exact superpose b16e86 b16e23
                | exact resolve b16e23 b16e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e114 : ∀ X0 : G, x = (M.op x (M.op y (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b16e15 x y X0
                   have i₂ := b16e86
                   grind)
                | exact superpose b16e86 b16e15
                | exact resolve b16e15 b16e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e86
              have b16e116 : x = y := by
                first
                | (have i₁ := b16e114 x
                   have i₂ := b16e34 x
                   grind)
                | exact superpose b16e34 b16e114
                | exact resolve b16e114 b16e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e34 b16e114
              have b16e118 : False := by grind
              exact b16e118
            · have b17e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b17e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e23 : y ≠ (M.op y x) := by grind
              have b17e24 : x = (M.op y y) := by grind
              have b17e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b17e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e47 : y = (k x y) ∨ y = (M.op y x) := by grind
              have b17e50 : y = (k x y) := by
                first
                | (have r₁ := b17e47
                   have r₂ := b17e23
                   grind)
                | exact resolve b17e47 b17e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e47
              have b17e65 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ y) X0) := by
                intro X0
                first
                | (have i₁ := b17e26
                   have i₂ := b17e20 X0 (σ y)
                   grind)
                | (have i₁ := b17e26
                   have i₂ := b17e20 (M.op (σ y) (σ y)) x
                   grind)
                | exact superpose b17e20 b17e26
                | (have j1 := b17e20 X0 (σ y)
                   grind)
                | (have r₁ := b17e26
                   have r₂ := b17e20 (σ x) (σ y)
                   grind)
                | exact resolve b17e26 b17e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b17e530 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have j0 := b17e65 (σ x)
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e65
              have b17e531 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b17e530
                   have r₂ := b17e25
                   grind)
                | exact resolve b17e530 b17e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e530
              have b17e532 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
                first
                | (have i₁ := b17e531
                   have i₂ := b17e21 x y
                   grind)
                | exact superpose b17e21 b17e531
                | exact resolve b17e531 b17e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e531
              have b17e533 : (σ y) = (M.op (σ y) (σ x)) := by
                first
                | (have i₁ := b17e532
                   have i₂ := b17e50
                   grind)
                | exact superpose b17e50 b17e532
                | exact resolve b17e532 b17e50
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e50 b17e532
              have b17e534 : False := by grind
              exact b17e534
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
        · have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ (M.op y y) := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e28 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b18e29 : (σ y) = (k (σ x) (σ y)) := by grind
          clear b18e28
          have b18e31 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b18e29
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e29
            | exact resolve b18e29 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29
          have b18e36 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e31
               grind)
            | exact superpose b18e31 b18e14
            | exact resolve b18e14 b18e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e31
          have b18e37 : y = (k x y) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e36
            | exact resolve b18e36 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e57 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e37
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e37
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e37 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e37
          have b18e69 : y = (M.op y x) ∨ x = (M.op y y) := by grind
          clear b18e57
          have b18e74 : x = (M.op y y) := by
            first
            | (have r₁ := b18e69
               have r₂ := b18e21
               grind)
            | exact resolve b18e69 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e69
          have b18e77 : False := by grind
          exact b18e77
        · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ (M.op y y) := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e29 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b19e30 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b19e29
            have b19e31 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e30
              | exact resolve b19e30 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : (k x y) = (τ (σ y)) := by
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
            have b19e33 : y = (k x y) := by
              first
              | (have i₁ := b19e32
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e32
              | exact resolve b19e32 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32
            have b19e61 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e33
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e33
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e33 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e33
            have b19e73 : y = (M.op y x) ∨ x = (M.op y y) := by grind
            clear b19e61
            have b19e78 : x = (M.op y y) := by
              first
              | (have r₁ := b19e73
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e73 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e73
            have b19e81 : False := by grind
            exact b19e81
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b20e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b20e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b20e22 : y ≠ (M.op y x) := by grind
            have b20e23 : x ≠ (M.op y y) := by grind
            have b20e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
            have b20e29 : (σ y) = (k (σ x) (σ y)) := by grind
            clear b20e28
            have b20e30 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b20e29
                 have i₂ := b20e20 x y
                 grind)
              | exact superpose b20e20 b20e29
              | exact resolve b20e29 b20e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e29
            have b20e31 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b20e15 (k x y)
                 have i₂ := b20e30
                 grind)
              | exact superpose b20e30 b20e15
              | exact resolve b20e15 b20e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e30
            have b20e32 : y = (k x y) := by
              first
              | (have i₁ := b20e31
                 have i₂ := b20e15 y
                 grind)
              | exact superpose b20e15 b20e31
              | exact resolve b20e31 b20e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e31
            have b20e80 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b20e32
                 have i₂ := b20e19 x y
                 grind)
              | exact superpose b20e19 b20e32
              | (have j1 := b20e19 x y
                 grind)
              | exact resolve b20e32 b20e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e32
            have b20e89 : y = (M.op y x) ∨ x = (M.op y y) := by grind
            clear b20e80
            have b20e93 : x = (M.op y y) := by
              first
              | (have r₁ := b20e89
                 have r₂ := b20e22
                 grind)
              | exact resolve b20e89 b20e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b20e89
            have b20e96 : False := by grind
            exact b20e96
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b21e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b21e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b21e22 : y ≠ (M.op y x) := by grind
            have b21e23 : x ≠ (M.op y y) := by grind
            have b21e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b21e25 : (σ x) = (M.op (σ y) (σ y)) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e46 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
            have b21e49 : (σ y) = (k (σ x) (σ y)) := by
              first
              | (have r₁ := b21e46
                 have r₂ := b21e24
                 grind)
              | exact resolve b21e46 b21e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e46
            have b21e50 : (σ y) = (σ (k x y)) := by
              first
              | (have i₁ := b21e49
                 have i₂ := b21e20 x y
                 grind)
              | exact superpose b21e20 b21e49
              | exact resolve b21e49 b21e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e49
            have b21e53 : (k x y) = (τ (σ y)) := by
              first
              | (have i₁ := b21e15 (k x y)
                 have i₂ := b21e50
                 grind)
              | exact superpose b21e50 b21e15
              | exact resolve b21e15 b21e50
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e50
            have b21e54 : y = (k x y) := by
              first
              | (have i₁ := b21e53
                 have i₂ := b21e15 y
                 grind)
              | exact superpose b21e15 b21e53
              | exact resolve b21e53 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e53
            have b21e80 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
              first
              | (have i₁ := b21e19 x y
                 have i₂ := b21e54
                 grind)
              | exact superpose b21e54 b21e19
              | (have j0 := b21e19 x y
                 grind)
              | exact resolve b21e19 b21e54
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e54
            have b21e81 : y = (M.op y x) ∨ x = (M.op y y) := by grind
            clear b21e80
            have b21e83 : x = (M.op y y) := by
              first
              | (have r₁ := b21e81
                 have r₂ := b21e22
                 grind)
              | exact resolve b21e81 b21e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e81
            have b21e85 : False := by grind
            exact b21e85
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e23 : y ≠ (M.op y x) := by grind
              have b22e24 : x ≠ (M.op y y) := by grind
              have b22e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b22e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e53 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
              have b22e56 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e53
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e53 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e53
              have b22e58 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b22e56
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e56
                | exact resolve b22e56 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e56
              have b22e82 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e58
                   grind)
                | exact superpose b22e58 b22e16
                | exact resolve b22e16 b22e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e58
              have b22e83 : y = (k x y) := by
                first
                | (have i₁ := b22e82
                   have i₂ := b22e16 y
                   grind)
                | exact superpose b22e16 b22e82
                | exact resolve b22e82 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e82
              have b22e105 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e83
                   grind)
                | exact superpose b22e83 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e83
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e83
              have b22e106 : y = (M.op y x) ∨ x = (M.op y y) := by grind
              clear b22e105
              have b22e108 : x = (M.op y y) := by
                first
                | (have r₁ := b22e106
                   have r₂ := b22e23
                   grind)
                | exact resolve b22e106 b22e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e106
              have b22e110 : False := by grind
              exact b22e110
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b23e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e23 : y ≠ (M.op y x) := by grind
              have b23e24 : x ≠ (M.op y y) := by grind
              have b23e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b23e26 : (σ x) = (M.op (σ y) (σ y)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e44 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
              have b23e47 : (σ y) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b23e44
                   have r₂ := b23e25
                   grind)
                | exact resolve b23e44 b23e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e44
              have b23e48 : (σ y) = (σ (k x y)) := by
                first
                | (have i₁ := b23e47
                   have i₂ := b23e21 x y
                   grind)
                | exact superpose b23e21 b23e47
                | exact resolve b23e47 b23e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e47
              have b23e51 : (k x y) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (k x y)
                   have i₂ := b23e48
                   grind)
                | exact superpose b23e48 b23e16
                | exact resolve b23e16 b23e48
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e48
              have b23e52 : y = (k x y) := by
                first
                | (have i₁ := b23e51
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e51
                | exact resolve b23e51 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e51
              have b23e74 : y = (M.op y x) ∨ x = (M.op y y) ∨ y = (M.op y x) := by
                first
                | (have i₁ := b23e20 x y
                   have i₂ := b23e52
                   grind)
                | exact superpose b23e52 b23e20
                | (have j0 := b23e20 x y
                   grind)
                | exact resolve b23e20 b23e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e52
              have b23e75 : y = (M.op y x) ∨ x = (M.op y y) := by grind
              clear b23e74
              have b23e77 : x = (M.op y y) := by
                first
                | (have r₁ := b23e75
                   have r₂ := b23e23
                   grind)
                | exact resolve b23e75 b23e23
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e75
              have b23e79 : False := by grind
              exact b23e79
        · rcases eq_or_ne (M.op x y) (x) with h2a | h2a
          · have b24e14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
              intro X0 X1 X2
              grind
            have b24e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b24e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b24e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
              intro X0 X1
              grind
            have b24e19 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e23 : x ≠ (M.op y y) := by grind
            have b24e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e25 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
            have b24e26 : x = (M.op x y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e28 : (σ x) ≠ (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e21
              | exact resolve b24e21 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e29 : x ≠ x ∨ x = (k y x) := by
              first
              | (have i₁ := b24e17 y x
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e17
              | (have j0 := b24e17 y x
                 grind)
              | (have r₁ := b24e17 y x
                 have r₂ := b24e26
                 grind)
              | exact resolve b24e17 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e30 : x = (k y x) := by grind
            clear b24e29
            have b24e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 (τ X0) X1
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 (τ X0)
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e20
              | exact resolve b24e20 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e33 : ∀ X0 : G, y = (M.op x (M.op x (M.op X0 X0))) := by
              intro X0
              first
              | (have i₁ := b24e14 y x X0
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e14
              | exact resolve b24e14 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e34 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
                 have i₂ := b24e14 X0 X1 X2
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e36 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                 have i₂ := b24e14 X0 (M.op X1 X1) X1
                 grind)
              | exact superpose b24e14 b24e14
              | exact resolve b24e14 b24e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e39 : ∀ X0 X1 : G, (M.op x (M.op X0 X0)) = (M.op y (M.op x (M.op X1 X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e14 (M.op x (M.op X0 X0)) x X1
                 have i₂ := b24e33 X0
                 grind)
              | exact superpose b24e33 b24e14
              | exact resolve b24e14 b24e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33
            have b24e46 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b24e15 (k (τ X0) X1)
                 have i₂ := b24e31 X0 X1
                 grind)
              | exact superpose b24e31 b24e15
              | exact resolve b24e15 b24e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e31
            have b24e51 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b24e20 X1 X0
                 have i₂ := b24e19 (σ X1) (σ X0)
                 grind)
              | exact superpose b24e19 b24e20
              | (have j1 := b24e19 (σ X1) (σ X0)
                 grind)
              | exact resolve b24e20 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e59 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X0) = X2 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X2 (M.op X1 X1) X1
                 have i₂ := b24e19 X0 (M.op X1 X1)
                 grind)
              | (have i₁ := b24e14 X0 X1 X2
                 have i₂ := b24e19 (M.op X1 (M.op X2 X2)) X1
                 grind)
              | exact superpose b24e19 b24e14
              | (have j1 := b24e19 X0 (M.op X1 X1)
                 grind)
              | exact resolve b24e14 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e83 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e36 X1 (M.op X0 X0) (M.op X0 X0)
                 have i₂ := b24e36 (M.op X0 X0) X0 X1
                 grind)
              | exact superpose b24e36 b24e36
              | exact resolve b24e36 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e85 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3))) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b24e14 X2 (M.op (M.op (M.op X1 X1) X2) X0) X3
                 have i₂ := b24e36 X2 X1 X0
                 grind)
              | exact superpose b24e36 b24e14
              | exact resolve b24e14 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e109 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 X1 X1 X2
                 have i₂ := b24e83 X0 X1
                 grind)
              | (have i₁ := b24e14 X1 X1 X2
                 have i₂ := b24e83 X1 X0
                 grind)
              | exact superpose b24e83 b24e14
              | exact resolve b24e14 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e113 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 ∨ (M.op X1 (M.op X0 X0)) = X1 := by
              intro X0 X1
              grind
            have b24e118 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X2) (M.op X1 X1)) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e36 (M.op X1 X1) X1 X2
                 have i₂ := b24e83 X0 (M.op X1 X1)
                 grind)
              | (have i₁ := b24e36 (M.op X1 X1) X1 X2
                 have i₂ := b24e83 (M.op X1 X1) X0
                 grind)
              | exact superpose b24e83 b24e36
              | exact resolve b24e36 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e119 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) X2) = (M.op (M.op X0 X0) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e36 X2 X0 (M.op (M.op X0 X0) X2)
                 have i₂ := b24e83 X1 (M.op (M.op X0 X0) X2)
                 grind)
              | (have i₁ := b24e36 X2 X0 (M.op (M.op X0 X0) X2)
                 have i₂ := b24e83 (M.op (M.op X0 X0) X2) X1
                 grind)
              | exact superpose b24e83 b24e36
              | exact resolve b24e36 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e121 : ∀ X0 : G, x ≠ (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b24e23
                 have i₂ := b24e83 X0 y
                 grind)
              | (have i₁ := b24e23
                 have i₂ := b24e83 y X0
                 grind)
              | exact superpose b24e83 b24e23
              | exact resolve b24e23 b24e83
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e122 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = X1 := by
              intro X0 X1
              first
              | (have j0 := b24e113 X0 X1
                 have j1 := b24e17 (M.op X0 X0) X1
                 grind)
              | (have r₁ := b24e113 X0 X1
                 have r₂ := b24e17 (M.op X0 X0) X1
                 grind)
              | exact resolve b24e113 b24e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e113
            have b24e152 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X1 X1) X2) X0) (M.op X3 X3)) = (M.op X2 (M.op X0 (M.op X4 X4))) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b24e34 X2 (M.op (M.op (M.op X1 X1) X2) X0) X3 X4
                 have i₂ := b24e36 X2 X1 X0
                 grind)
              | exact superpose b24e36 b24e34
              | exact resolve b24e34 b24e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e36
            have b24e170 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X2)) = (M.op X0 (M.op X1 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e34 x X0 X2 x
                 have i₂ := b24e34 x X0 X1 x
                 grind)
              | (have i₁ := b24e34 X1 X1 X2 X1
                 have i₂ := b24e34 X0 X1 (M.op X1 X1) x
                 grind)
              | exact superpose b24e34 b24e34
              | exact resolve b24e34 b24e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e34
            have b24e295 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op X1 X1)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e46 (M.op X1 X1) X0
                 have i₂ := b24e122 X1 (σ X0)
                 grind)
              | exact superpose b24e122 b24e46
              | exact resolve b24e46 b24e122
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e46 b24e122
            have b24e305 : ∀ X0 X1 : G, (k (τ (M.op X1 X1)) X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b24e295 X0 X1
                 have i₂ := b24e15 X0
                 grind)
              | exact superpose b24e15 b24e295
              | exact resolve b24e295 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e295
            have b24e526 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X1) (M.op X2 X2))) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e14 (σ X0) (σ X1) X2
                 have i₂ := b24e51 X1 X0
                 grind)
              | exact superpose b24e51 b24e14
              | (have j1 := b24e51 X1 X0
                 grind)
              | exact resolve b24e14 b24e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e581 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e51 X0 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b24e582 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have j0 := b24e51 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e51
            have b24e583 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b24e581 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e581
            have b24e1661 : ∀ X0 X1 : G, x = (M.op (M.op X1 X1) (M.op y (M.op x (M.op X0 X0)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e109 X1 x x
                 have i₂ := b24e39 x X0
                 grind)
              | exact superpose b24e39 b24e109
              | exact resolve b24e109 b24e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e109
            have b24e3140 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b24e583 (τ X0)
                 have i₂ := b24e32 X0 (τ X0)
                 grind)
              | exact superpose b24e32 b24e583
              | (have j0 := b24e583 (τ X0)
                 grind)
              | exact resolve b24e583 b24e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32 b24e583
            have b24e3153 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b24e3140 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e3140
              | (have j0 := b24e3140 X0
                 grind)
              | exact resolve b24e3140 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3140
            have b24e3162 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e3153 X0
                 have i₂ := b24e16 X0
                 grind)
              | exact superpose b24e16 b24e3153
              | (have j0 := b24e3153 X0
                 grind)
              | exact resolve b24e3153 b24e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3153
            have b24e5014 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X2 X2)))) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e85 X1 x X0 x
                 have i₂ := b24e152 X1 x X0 x X2
                 grind)
              | exact superpose b24e152 b24e85
              | exact resolve b24e85 b24e152
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e152
            have b24e5632 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X0) (M.op X2 X0)) = X2 := by
              intro X0 X1 X2
              first
              | (have i₁ := b24e5014 X2 (M.op (M.op X1 X1) X0) x
                 have i₂ := b24e118 X1 x X0
                 grind)
              | exact superpose b24e118 b24e5014
              | exact resolve b24e5014 b24e118
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e118 b24e5014
            have b24e7891 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ (M.op (M.op X0 X0) (M.op y (M.op x (M.op X1 X1)))) = (k (M.op y (M.op x (M.op X1 X1))) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op y (M.op x (M.op X1 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e59 (M.op y (M.op x (M.op X1 X1))) X0 (M.op X0 X0)
                 have i₂ := b24e1661 X1 (M.op X0 X0)
                 grind)
              | exact superpose b24e1661 b24e59
              | (have j0 := b24e59 (M.op y (M.op x (M.op X1 X1))) X0 x
                 grind)
              | exact resolve b24e59 b24e1661
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e59
            have b24e7915 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op y (M.op x (M.op X1 X1)))) = (k (M.op y (M.op x (M.op X1 X1))) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op y (M.op x (M.op X1 X1)))) := by
              intro X0 X1
              first
              | (have j0 := b24e7891 X0 X1
                 grind)
              | (have r₁ := b24e7891 X0 X1
                 have r₂ := b24e121 X0
                 grind)
              | exact resolve b24e7891 b24e121
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e7891
            have b24e7930 : ∀ X0 X1 : G, x = (k (M.op y (M.op x (M.op X1 X1))) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op y (M.op x (M.op X1 X1)))) := by
              intro X0 X1
              first
              | (have i₁ := b24e7915 X0 X1
                 have i₂ := b24e1661 X1 X0
                 grind)
              | exact superpose b24e1661 b24e7915
              | (have j0 := b24e7915 X0 X1
                 grind)
              | exact resolve b24e7915 b24e1661
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e7915
            have b24e7932 : ∀ X0 X1 : G, x = (M.op X0 X0) ∨ x = (k (M.op y (M.op x (M.op X1 X1))) (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b24e7930 X0 X1
                 have i₂ := b24e1661 X1 X0
                 grind)
              | exact superpose b24e1661 b24e7930
              | (have j0 := b24e7930 X0 X1
                 grind)
              | exact resolve b24e7930 b24e1661
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1661 b24e7930
            have b24e7934 : ∀ X0 X1 : G, x = (k (M.op y (M.op x (M.op X1 X1))) (M.op X0 X0)) := by
              intro X0 X1
              first
              | (have j0 := b24e7932 X0 X1
                 grind)
              | (have r₁ := b24e7932 X0 X1
                 have r₂ := b24e121 X0
                 grind)
              | exact resolve b24e7932 b24e121
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e121 b24e7932
            have b24e12291 : ∀ X0 X2 : G, x = (k (M.op x (M.op X0 X0)) (M.op X2 X2)) := by
              intro X0 X2
              first
              | (have i₁ := b24e7934 X2 x
                 have i₂ := b24e39 X0 x
                 grind)
              | exact superpose b24e39 b24e7934
              | exact resolve b24e7934 b24e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e39 b24e7934
            have b24e17240 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e582 x y
                 have i₂ := b24e30
                 grind)
              | exact superpose b24e30 b24e582
              | (have j0 := b24e582 x y
                 grind)
              | exact resolve b24e582 b24e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e30 b24e582
            have b24e17245 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
            clear b24e17240
            have b24e17269 : (σ y) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b24e17245
                 have r₂ := b24e28
                 grind)
              | exact resolve b24e17245 b24e28
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17245
            have b24e17318 : ∀ X0 : G, (σ y) = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b24e83 (σ x) X0
                 have i₂ := b24e17269
                 grind)
              | exact superpose b24e17269 b24e83
              | exact resolve b24e83 b24e17269
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e83
            have b24e17329 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b24e119 (σ x) X0 X1
                 have i₂ := b24e17269
                 grind)
              | exact superpose b24e17269 b24e119
              | exact resolve b24e119 b24e17269
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e119
            have b24e17344 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
              intro X0 X1
              first
              | (have i₁ := b24e170 X0 (σ x) X1
                 have i₂ := b24e17269
                 grind)
              | exact superpose b24e17269 b24e170
              | exact resolve b24e170 b24e17269
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e170
            have b24e17364 : ∀ X0 : G, (k (τ (σ y)) X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e305 X0 (σ x)
                 have i₂ := b24e17269
                 grind)
              | exact superpose b24e17269 b24e305
              | exact resolve b24e305 b24e17269
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e305 b24e17269
            have b24e17440 : ∀ X0 : G, (k y X0) = X0 := by
              intro X0
              first
              | (have i₁ := b24e17364 X0
                 have i₂ := b24e15 y
                 grind)
              | exact superpose b24e15 b24e17364
              | exact resolve b24e17364 b24e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17364
            have b24e19873 : y ≠ y ∨ y = (M.op y y) := by
              first
              | (have i₁ := b24e3162 y
                 have i₂ := b24e17440 y
                 grind)
              | exact superpose b24e17440 b24e3162
              | (have j0 := b24e3162 y
                 grind)
              | (have r₁ := b24e3162 y
                 have r₂ := b24e17440 y
                 grind)
              | exact resolve b24e3162 b24e17440
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e3162 b24e17440
            have b24e19902 : y = (M.op y y) := by grind
            clear b24e19873
            have b24e19927 : y = (σ y) := by
              first
              | (have i₁ := b24e19902
                 have i₂ := b24e17318 y
                 grind)
              | exact superpose b24e17318 b24e19902
              | exact resolve b24e19902 b24e17318
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e19902
            have b24e32796 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (σ y)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e85 (M.op (M.op X0 X0) X1) X0 X1 (M.op (M.op X0 X0) X1)
                 have i₂ := b24e17318 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))
                 grind)
              | exact superpose b24e17318 b24e85
              | exact resolve b24e85 b24e17318
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e85
            have b24e32852 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b24e32796 X0 X1
                 have i₂ := b24e19927
                 grind)
              | exact superpose b24e19927 b24e32796
              | exact resolve b24e32796 b24e19927
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32796
            have b24e33021 : ∀ X1 : G, (M.op (M.op (σ y) X1) y) = X1 := by
              intro X1
              first
              | (have i₁ := b24e32852 x X1
                 have i₂ := b24e17329 x X1
                 grind)
              | exact superpose b24e17329 b24e32852
              | exact resolve b24e32852 b24e17329
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e32852
            have b24e33124 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
              intro X1
              first
              | (have i₁ := b24e33021 X1
                 have i₂ := b24e19927
                 grind)
              | exact superpose b24e19927 b24e33021
              | exact resolve b24e33021 b24e19927
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33021
            have b24e48012 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 := by
              intro X0
              first
              | (have i₁ := b24e5632 y y X0
                 have i₂ := b24e33124 y
                 grind)
              | exact superpose b24e33124 b24e5632
              | exact resolve b24e5632 b24e33124
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e33124
            have b24e48839 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X1 X1) (M.op X0 y)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b24e5632 (M.op X0 y) X1 y
                 have i₂ := b24e48012 X0
                 grind)
              | exact superpose b24e48012 b24e5632
              | exact resolve b24e5632 b24e48012
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e5632
            have b24e48840 : ∀ X0 : G, y = (M.op (M.op (σ y) (M.op X0 y)) X0) := by
              intro X0
              first
              | (have i₁ := b24e48839 X0 x
                 have i₂ := b24e17329 x (M.op X0 y)
                 grind)
              | exact superpose b24e17329 b24e48839
              | exact resolve b24e48839 b24e17329
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17329 b24e48839
            have b24e48885 : ∀ X0 : G, y = (M.op (M.op y (M.op X0 y)) X0) := by
              intro X0
              first
              | (have i₁ := b24e48840 X0
                 have i₂ := b24e19927
                 grind)
              | exact superpose b24e19927 b24e48840
              | exact resolve b24e48840 b24e19927
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e48840
            have b24e48924 : ∀ X0 : G, y = (M.op X0 X0) := by
              intro X0
              first
              | (have i₁ := b24e48885 X0
                 have i₂ := b24e48012 X0
                 grind)
              | exact superpose b24e48012 b24e48885
              | exact resolve b24e48885 b24e48012
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e48012 b24e48885
            have b24e50020 : ∀ X1 : G, x = (k (M.op x y) (M.op X1 X1)) := by
              intro X1
              first
              | (have i₁ := b24e12291 x X1
                 have i₂ := b24e48924 x
                 grind)
              | exact superpose b24e48924 b24e12291
              | exact resolve b24e12291 b24e48924
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e12291 b24e48924
            have b24e50306 : x = (k (M.op x y) (σ y)) := by
              first
              | (have i₁ := b24e50020 x
                 have i₂ := b24e17318 x
                 grind)
              | exact superpose b24e17318 b24e50020
              | exact resolve b24e50020 b24e17318
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17318 b24e50020
            have b24e50527 : x = (k (M.op x y) y) := by
              first
              | (have i₁ := b24e50306
                 have i₂ := b24e19927
                 grind)
              | exact superpose b24e19927 b24e50306
              | exact resolve b24e50306 b24e19927
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e19927 b24e50306
            have b24e50672 : x = (k x y) := by
              first
              | (have i₁ := b24e50527
                 have i₂ := b24e26
                 grind)
              | exact superpose b24e26 b24e50527
              | exact resolve b24e50527 b24e26
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e50527
            have b24e84187 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              intro X0
              first
              | (have i₁ := b24e526 x y X0
                 have i₂ := b24e50672
                 grind)
              | exact superpose b24e50672 b24e526
              | (have j0 := b24e526 x y x
                 grind)
              | exact resolve b24e526 b24e50672
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e526 b24e50672
            have b24e84487 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) ∨ (σ y) = (M.op (σ y) (σ x)) := by
              intro X0
              first
              | (have j0 := b24e84187 X0
                 grind)
              | (have r₁ := b24e84187 X0
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e84187 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e84187
            have b24e84639 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ y) (M.op X0 X0))) := by
              intro X0
              first
              | (have j0 := b24e84487 X0
                 grind)
              | (have r₁ := b24e84487 X0
                 have r₂ := b24e24
                 grind)
              | exact resolve b24e84487 b24e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e84487
            have b24e84772 : (σ x) = (M.op (σ x) (M.op (σ y) (σ y))) := by
              first
              | (have i₁ := b24e84639 x
                 have i₂ := b24e17344 (σ y) x
                 grind)
              | exact superpose b24e17344 b24e84639
              | exact resolve b24e84639 b24e17344
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e84639
            have b24e84900 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b24e84772
                 have i₂ := b24e17344 (σ x) (σ y)
                 grind)
              | exact superpose b24e17344 b24e84772
              | exact resolve b24e84772 b24e17344
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e17344 b24e84772
            have b24e85004 : False := by grind
            exact b24e85004
          · rcases eq_or_ne (M.op x x) (y) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e24 : x ≠ (M.op y y) := by grind
              have b25e26 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
              have b25e28 : y = (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 (τ X0) X1
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e21
                | exact resolve b25e21 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
                intro X0 X1
                first
                | (have i₁ := b25e16 (k (τ X0) X1)
                   have i₂ := b25e31 X0 X1
                   grind)
                | exact superpose b25e31 b25e16
                | exact resolve b25e16 b25e31
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e37 : ∀ X0 : G, x = (M.op y (M.op x (M.op X0 X0))) := by
                intro X0
                first
                | (have i₁ := b25e15 x x X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e38 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) (M.op X3 X3))) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e15 (M.op X1 (M.op X2 X2)) (M.op X1 X0) X3
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 y)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 X0 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e41 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                   have i₂ := b25e15 X0 (M.op X1 X1) X1
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e43 : x = (M.op y (M.op x y)) := by
                first
                | (have i₁ := b25e37 x
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e37
                | exact resolve b25e37 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e55 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e60 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e63 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) X0) = X2 ∨ (M.op (M.op X1 X1) X0) = (k X0 (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 (M.op X1 X1) X1
                   have i₂ := b25e20 X0 (M.op X1 X1)
                   grind)
                | (have i₁ := b25e15 X0 X1 X2
                   have i₂ := b25e20 (M.op X1 (M.op X2 X2)) X1
                   grind)
                | exact superpose b25e20 b25e15
                | (have j1 := b25e20 X0 (M.op X1 X1)
                   grind)
                | exact resolve b25e15 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e66 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b25e60 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e60
              have b25e69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b25e66 X0 X1
                   have j1 := b25e18 X0 X1
                   grind)
                | (have r₁ := b25e66 X0 X1
                   have r₂ := b25e18 X0 X1
                   grind)
                | exact resolve b25e66 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e66
              have b25e73 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X0 (M.op (M.op X1 X0) y)) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e39 (M.op X1 X0) (M.op X1 (M.op X2 X2))
                   have i₂ := b25e15 X0 X1 X2
                   grind)
                | exact superpose b25e15 b25e39
                | exact resolve b25e39 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e74 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e39 (M.op X1 X0) (M.op X1 y)
                   have i₂ := b25e39 X1 X0
                   grind)
                | exact superpose b25e39 b25e39
                | exact resolve b25e39 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e76 : ∀ X0 : G, (M.op x (M.op X0 X0)) = (M.op x (M.op y y)) := by
                intro X0
                first
                | (have i₁ := b25e39 y (M.op x (M.op X0 X0))
                   have i₂ := b25e37 X0
                   grind)
                | exact superpose b25e37 b25e39
                | exact resolve b25e39 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e77 : (M.op x y) = (M.op x (M.op y y)) := by
                first
                | (have i₁ := b25e39 y (M.op x y)
                   have i₂ := b25e43
                   grind)
                | exact superpose b25e43 b25e39
                | exact resolve b25e39 b25e43
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e43
              have b25e79 : ∀ X0 X1 : G, (M.op (M.op (M.op y X0) X1) X0) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 (M.op y X0) y
                   have i₂ := b25e39 y X0
                   grind)
                | exact superpose b25e39 b25e15
                | exact resolve b25e15 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e84 : ∀ X0 X1 X2 : G, (M.op X1 y) = (M.op X0 (M.op (M.op X1 X0) (M.op X2 X2))) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 (M.op X1 y) (M.op X1 X0) X2
                   have i₂ := b25e39 X1 X0
                   grind)
                | exact superpose b25e39 b25e15
                | exact resolve b25e15 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e87 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e76 X0
                   have i₂ := b25e77
                   grind)
                | exact superpose b25e77 b25e76
                | exact resolve b25e76 b25e77
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e76 b25e77
              have b25e88 : ∀ X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op X1 y) := by
                intro X1 X2
                first
                | (have i₁ := b25e73 x X1 X2
                   have i₂ := b25e74 x X1
                   grind)
                | exact superpose b25e74 b25e73
                | exact resolve b25e73 b25e74
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e73 b25e74
              have b25e92 : ∀ X0 : G, (M.op y y) = (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b25e79 X0 (M.op y y)
                   have i₂ := b25e39 y X0
                   grind)
                | exact superpose b25e39 b25e79
                | exact resolve b25e79 b25e39
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e95 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op y X1) X0) (M.op X2 X2))) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X1 (M.op (M.op y X1) X0) X2
                   have i₂ := b25e79 X1 X0
                   grind)
                | exact superpose b25e79 b25e15
                | exact resolve b25e15 b25e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e100 : ∀ X1 : G, (M.op (M.op y X1) y) = X1 := by
                intro X1
                first
                | (have i₁ := b25e95 x X1 x
                   have i₂ := b25e84 x (M.op y X1) x
                   grind)
                | exact superpose b25e84 b25e95
                | exact resolve b25e95 b25e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e84 b25e95
              have b25e123 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) y) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e79 y X1
                   have i₂ := b25e92 X0
                   grind)
                | (have i₁ := b25e79 y X1
                   have i₂ := b25e92 y
                   grind)
                | exact superpose b25e92 b25e79
                | exact resolve b25e79 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e132 : ∀ X0 : G, (k (M.op y y) X0) = X0 ∨ (M.op X0 (M.op y y)) = X0 := by
                intro X0
                grind
              have b25e135 : ∀ X0 : G, (M.op (M.op y y) (M.op X0 y)) = X0 := by
                intro X0
                first
                | (have i₁ := b25e39 X0 X0
                   have i₂ := b25e92 X0
                   grind)
                | (have i₁ := b25e39 y y
                   have i₂ := b25e92 X0
                   grind)
                | exact superpose b25e92 b25e39
                | exact resolve b25e39 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e142 : (σ x) ≠ (M.op y y) := by
                first
                | (have i₁ := b25e26
                   have i₂ := b25e92 (σ y)
                   grind)
                | exact superpose b25e92 b25e26
                | exact resolve b25e26 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e143 : y = (M.op y y) := by
                first
                | (have i₁ := b25e28
                   have i₂ := b25e92 x
                   grind)
                | exact superpose b25e92 b25e28
                | exact resolve b25e28 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e144 : y ≠ (σ x) := by
                first
                | (have i₁ := b25e142
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e142
                | exact resolve b25e142 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e142
              have b25e148 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 := by
                intro X0
                first
                | (have i₁ := b25e135 X0
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e135
                | exact resolve b25e135 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e135
              have b25e149 : ∀ X0 : G, (k (M.op y y) X0) = X0 := by
                intro X0
                first
                | (have j0 := b25e132 X0
                   have j1 := b25e18 (M.op y y) X0
                   grind)
                | (have r₁ := b25e132 x
                   have r₂ := b25e18 (M.op y y) x
                   grind)
                | exact resolve b25e132 b25e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e132
              have b25e157 : ∀ X0 : G, (k y X0) = X0 := by
                intro X0
                first
                | (have i₁ := b25e149 X0
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e149
                | exact resolve b25e149 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e149
              have b25e173 : ∀ X0 : G, y = (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b25e41 X0 y y
                   have i₂ := b25e79 y X0
                   grind)
                | exact superpose b25e79 b25e41
                | exact resolve b25e41 b25e79
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e41 b25e79
              have b25e195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e69 (σ X0) (σ X1)
                   have i₂ := b25e21 X0 X1
                   grind)
                | exact superpose b25e21 b25e69
                | exact resolve b25e69 b25e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e69
              have b25e224 : x ≠ y := by
                first
                | (have i₁ := b25e24
                   have i₂ := b25e173 y
                   grind)
                | exact superpose b25e173 b25e24
                | exact resolve b25e24 b25e173
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e294 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) (M.op X2 y)) := by
                intro X0 X1 X2 X3
                first
                | (have i₁ := b25e39 X2 (M.op (M.op X0 X2) (M.op X3 X3))
                   have i₂ := b25e38 X2 X0 X1 X3
                   grind)
                | (have i₁ := b25e39 X1 (M.op X2 X2)
                   have i₂ := b25e38 X0 X1 X2 X3
                   grind)
                | exact superpose b25e38 b25e39
                | exact resolve b25e39 b25e38
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e38
              have b25e308 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 X3)) = (M.op (M.op X0 y) (M.op X2 y)) := by
                intro X0 X2 X3
                first
                | (have i₁ := b25e294 X0 x X2 X3
                   have i₂ := b25e88 X0 x
                   grind)
                | exact superpose b25e88 b25e294
                | exact resolve b25e294 b25e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e294
              have b25e368 : ∀ X0 X2 : G, (M.op (M.op X0 X2) y) = (M.op (M.op X0 y) (M.op X2 y)) := by
                intro X0 X2
                first
                | (have i₁ := b25e308 X0 X2 x
                   have i₂ := b25e88 (M.op X0 X2) x
                   grind)
                | exact superpose b25e88 b25e308
                | exact resolve b25e308 b25e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e308
              have b25e950 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e55 X0 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e55
              have b25e952 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                first
                | (have j0 := b25e950 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e950
              have b25e973 : ∀ X0 : G, (σ X0) = (M.op y y) ∨ (σ X0) ≠ (σ (k X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e952 X0
                   have i₂ := b25e92 (σ X0)
                   grind)
                | exact superpose b25e92 b25e952
                | (have j0 := b25e952 X0
                   grind)
                | exact resolve b25e952 b25e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e92 b25e952
              have b25e1027 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = y := by
                intro X0
                first
                | (have i₁ := b25e973 X0
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e973
                | (have j0 := b25e973 X0
                   grind)
                | exact resolve b25e973 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e143 b25e973
              have b25e2366 : (σ y) ≠ (σ y) ∨ y = (σ y) := by
                first
                | (have i₁ := b25e1027 y
                   have i₂ := b25e157 y
                   grind)
                | exact superpose b25e157 b25e1027
                | (have j0 := b25e1027 y
                   grind)
                | exact resolve b25e1027 b25e157
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e157 b25e1027
              have b25e2370 : y = (σ y) := by grind
              clear b25e2366
              have b25e2406 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e2370
                   grind)
                | exact superpose b25e2370 b25e22
                | exact resolve b25e22 b25e2370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e2416 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 y)) := by
                intro X0
                first
                | (have i₁ := b25e36 X0 y
                   have i₂ := b25e2370
                   grind)
                | exact superpose b25e2370 b25e36
                | exact resolve b25e36 b25e2370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e36
              have b25e2860 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X0) X1) y) ∨ (M.op (M.op X0 X0) (M.op X1 y)) = (k (M.op X1 y) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e63 (M.op X1 y) X0 y
                   have i₂ := b25e368 (M.op X0 X0) X1
                   grind)
                | exact superpose b25e368 b25e63
                | (have j0 := b25e63 (M.op X1 y) X0 x
                   grind)
                | exact resolve b25e63 b25e368
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e63 b25e368
              have b25e2926 : ∀ X0 X1 : G, y = X1 ∨ (M.op (M.op X0 X0) (M.op X1 y)) = (k (M.op X1 y) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e2860 X0 X1
                   have i₂ := b25e123 X0 X1
                   grind)
                | exact superpose b25e123 b25e2860
                | (have j0 := b25e2860 X0 X1
                   grind)
                | exact resolve b25e2860 b25e123
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e123 b25e2860
              have b25e2960 : ∀ X0 X1 : G, (M.op y (M.op X1 y)) = (k (M.op X1 y) y) ∨ y = X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e2926 X0 X1
                   have i₂ := b25e173 X0
                   grind)
                | exact superpose b25e173 b25e2926
                | (have j0 := b25e2926 X0 X1
                   grind)
                | exact resolve b25e2926 b25e173
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2926
              have b25e2970 : ∀ X0 X1 : G, (k (M.op X1 y) y) = X1 ∨ y = X1 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X1 y)) := by
                intro X0 X1
                first
                | (have i₁ := b25e2960 X0 X1
                   have i₂ := b25e148 X1
                   grind)
                | exact superpose b25e148 b25e2960
                | (have j0 := b25e2960 X0 X1
                   grind)
                | exact resolve b25e2960 b25e148
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2960
              have b25e2972 : ∀ X1 : G, y = (M.op y (M.op X1 y)) ∨ (k (M.op X1 y) y) = X1 ∨ y = X1 := by
                intro X1
                first
                | (have i₁ := b25e2970 x X1
                   have i₂ := b25e173 x
                   grind)
                | exact superpose b25e173 b25e2970
                | (have j0 := b25e2970 x X1
                   grind)
                | exact resolve b25e2970 b25e173
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e173 b25e2970
              have b25e2974 : ∀ X1 : G, y = X1 ∨ (k (M.op X1 y) y) = X1 ∨ y = X1 := by
                intro X1
                first
                | (have i₁ := b25e2972 X1
                   have i₂ := b25e148 X1
                   grind)
                | exact superpose b25e148 b25e2972
                | (have j0 := b25e2972 X1
                   grind)
                | exact resolve b25e2972 b25e148
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e148 b25e2972
              have b25e2975 : ∀ X1 : G, (k (M.op X1 y) y) = X1 ∨ y = X1 := by
                intro X1
                first
                | (have j0 := b25e2974 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2974
              have b25e4681 : ∀ X0 : G, (M.op y X0) = (k X0 y) ∨ y = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b25e2975 (M.op y X0)
                   have i₂ := b25e100 X0
                   grind)
                | exact superpose b25e100 b25e2975
                | (have j0 := b25e2975 (M.op y X0)
                   grind)
                | exact resolve b25e2975 b25e100
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e100 b25e2975
              have b25e5088 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X1) y)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e39 (σ X1) (σ X0)
                   have i₂ := b25e195 X0 X1
                   grind)
                | exact superpose b25e195 b25e39
                | (have j1 := b25e195 X0 X1
                   grind)
                | exact resolve b25e39 b25e195
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e39 b25e195
              have b25e27254 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op y X0)) ∨ y = (M.op y X0) := by
                intro X0
                first
                | (have i₁ := b25e2416 X0
                   have i₂ := b25e4681 X0
                   grind)
                | exact superpose b25e4681 b25e2416
                | (have j1 := b25e4681 X0
                   grind)
                | exact resolve b25e2416 b25e4681
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2416 b25e4681
              have b25e211803 : ∀ X0 : G, (τ x) = (k (τ (M.op x (M.op X0 X0))) y) ∨ x = y := by
                intro X0
                first
                | (have i₁ := b25e27254 (M.op x (M.op X0 X0))
                   have i₂ := b25e37 X0
                   grind)
                | exact superpose b25e37 b25e27254
                | exact resolve b25e27254 b25e37
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e37 b25e27254
              have b25e211983 : ∀ X0 : G, (τ x) = (k (τ (M.op x (M.op X0 X0))) y) := by
                intro X0
                first
                | (have j0 := b25e211803 X0
                   grind)
                | (have r₁ := b25e211803 X0
                   have r₂ := b25e224
                   grind)
                | exact resolve b25e211803 b25e224
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e224 b25e211803
              have b25e212004 : (τ x) = (k (τ (M.op x y)) y) := by
                first
                | (have i₁ := b25e211983 x
                   have i₂ := b25e87 x
                   grind)
                | exact superpose b25e87 b25e211983
                | exact resolve b25e211983 b25e87
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e87 b25e211983
              have b25e213031 : (k (M.op x y) (σ y)) = (σ (τ x)) := by
                first
                | (have i₁ := b25e31 (M.op x y) y
                   have i₂ := b25e212004
                   grind)
                | exact superpose b25e212004 b25e31
                | exact resolve b25e31 b25e212004
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e31 b25e212004
              have b25e213102 : x = (k (M.op x y) (σ y)) := by
                first
                | (have i₁ := b25e213031
                   have i₂ := b25e17 x
                   grind)
                | exact superpose b25e17 b25e213031
                | exact resolve b25e213031 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e213031
              have b25e213126 : x = (k (M.op x y) y) := by
                first
                | (have i₁ := b25e213102
                   have i₂ := b25e2370
                   grind)
                | exact superpose b25e2370 b25e213102
                | exact resolve b25e213102 b25e2370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e213102
              have b25e214087 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e5088 (M.op x y) y
                   have i₂ := b25e213126
                   grind)
                | exact superpose b25e213126 b25e5088
                | exact resolve b25e5088 b25e213126
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e5088 b25e213126
              have b25e214100 : (σ (M.op x y)) = (M.op (σ x) (M.op y y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e214087
                   have i₂ := b25e2370
                   grind)
                | exact superpose b25e2370 b25e214087
                | exact resolve b25e214087 b25e2370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e214087
              have b25e214106 : (σ (M.op x y)) = (M.op (σ x) y) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e214100
                   have i₂ := b25e88 (σ x) y
                   grind)
                | exact superpose b25e88 b25e214100
                | exact resolve b25e214100 b25e88
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e88 b25e214100
              have b25e214110 : (σ x) = (σ y) := by
                first
                | (have r₁ := b25e214106
                   have r₂ := b25e2406
                   grind)
                | exact resolve b25e214106 b25e2406
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2406 b25e214106
              have b25e214113 : y = (σ x) := by
                first
                | (have i₁ := b25e214110
                   have i₂ := b25e2370
                   grind)
                | exact superpose b25e2370 b25e214110
                | exact resolve b25e214110 b25e2370
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e2370 b25e214110
              have b25e214115 : False := by grind
              exact b25e214115
            · have b26e15 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 (M.op X2 X2))) = X0 := by
                intro X0 X1 X2
                grind
              have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e27 : x ≠ (M.op x y) := by grind
              have b26e28 : y ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
              have b26e34 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X1) X0) X2) X0) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e15 X2 (M.op (M.op X1 X1) X0) (M.op X1 X1)
                   have i₂ := b26e15 X0 (M.op X1 X1) X1
                   grind)
                | exact superpose b26e15 b26e15
                | exact resolve b26e15 b26e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e60 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b26e65 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                first
                | (have j0 := b26e60 X0 X1
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e60
              have b26e66 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have j0 := b26e65 X0 X1
                   have j1 := b26e18 X0 X1
                   grind)
                | (have r₁ := b26e65 X0 X1
                   have r₂ := b26e18 X0 X1
                   grind)
                | exact resolve b26e65 b26e18
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e65
              have b26e84 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b26e34 X1 (M.op X0 X0) (M.op X0 X0)
                   have i₂ := b26e34 (M.op X0 X0) X0 X1
                   grind)
                | exact superpose b26e34 b26e34
                | exact resolve b26e34 b26e34
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e34
              have b26e113 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X2 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X1 X2) = X1 := by
                intro X0 X1 X2
                first
                | (have i₁ := b26e20 X2 X1
                   have i₂ := b26e84 X0 X1
                   grind)
                | (have i₁ := b26e20 X2 X1
                   have i₂ := b26e84 X1 X0
                   grind)
                | exact superpose b26e84 b26e20
                | (have j0 := b26e20 X2 X1
                   grind)
                | exact resolve b26e20 b26e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e121 : ∀ X0 : G, y ≠ (M.op X0 X0) := by
                intro X0
                first
                | (have i₁ := b26e28
                   have i₂ := b26e84 X0 x
                   grind)
                | (have i₁ := b26e28
                   have i₂ := b26e84 x X0
                   grind)
                | exact superpose b26e84 b26e28
                | exact resolve b26e28 b26e84
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e84
              have b26e125 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e66 (σ X0) (σ X1)
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e66
                | exact resolve b26e66 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e130 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (k (τ X1) X0) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b26e30 X1 X0
                   have i₂ := b26e66 (τ X1) X0
                   grind)
                | exact superpose b26e66 b26e30
                | (have j1 := b26e66 (τ X1) X0
                   grind)
                | exact resolve b26e30 b26e66
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e30 b26e66
              have b26e2485 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e130 X0 (σ X0)
                   have i₂ := b26e16 X0
                   grind)
                | exact superpose b26e16 b26e130
                | exact resolve b26e130 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e130
              have b26e2530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b26e2485 X0 X1
                   have i₂ := b26e21 X0 X1
                   grind)
                | exact superpose b26e21 b26e2485
                | (have j0 := b26e2485 X0 X1
                   grind)
                | exact resolve b26e2485 b26e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2485
              have b26e2861 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e125 y x
                   grind)
                | exact superpose b26e125 b26e22
                | (have j1 := b26e125 y x
                   grind)
                | exact resolve b26e22 b26e125
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e125
              have b26e148829 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
                first
                | (have i₁ := b26e2861
                   have i₂ := b26e2530 y x
                   grind)
                | exact superpose b26e2530 b26e2861
                | (have j1 := b26e2530 y x
                   grind)
                | (have r₁ := b26e2861
                   have r₂ := b26e2530 y x
                   grind)
                | exact resolve b26e2861 b26e2530
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e2530 b26e2861
              have b26e148830 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by grind
              clear b26e148829
              have b26e299904 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
                first
                | (have i₁ := b26e16 (M.op x y)
                   have i₂ := b26e148830
                   grind)
                | exact superpose b26e148830 b26e16
                | exact resolve b26e16 b26e148830
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e148830
              have b26e299905 : x = (M.op x y) ∨ x = (k y x) := by
                first
                | (have i₁ := b26e299904
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e299904
                | exact resolve b26e299904 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e299904
              have b26e299906 : x = (k y x) := by
                first
                | (have r₁ := b26e299905
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e299905 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e299905
              have b26e299911 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 X0) ∨ x = (M.op x y) := by
                intro X0
                first
                | (have i₁ := b26e113 X0 x y
                   have i₂ := b26e299906
                   grind)
                | exact superpose b26e299906 b26e113
                | (have j0 := b26e113 X0 x y
                   grind)
                | exact resolve b26e113 b26e299906
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e113 b26e299906
              have b26e299912 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op X0 X0) := by
                intro X0
                first
                | (have j0 := b26e299911 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e299911
              have b26e299916 : ∀ X0 : G, y = (M.op X0 X0) := by
                intro X0
                first
                | (have j0 := b26e299912 X0
                   grind)
                | (have r₁ := b26e299912 X0
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e299912 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e299912
              have b26e299920 : False := by grind
              exact b26e299920

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_x_pxy_Equation2146 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
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
      have b0e33 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 x X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (M.op X1 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
           have i₂ := b0e11 X0 X1 (M.op X1 X1)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
           have i₂ := b0e11 X0 X3 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op y (M.op X0 X1)) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 (M.op X0 X1) (M.op (M.op X2 X2) X1)
           have i₂ := b0e11 X0 X2 X1
           grind)
        | exact superpose b0e11 b0e33
        | exact resolve b0e33 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X1)) X0) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 (M.op X0 X1) (M.op y X1)
           have i₂ := b0e33 X1 X0
           grind)
        | exact superpose b0e33 b0e33
        | exact resolve b0e33 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op y X2) X1 (M.op X0 X2)
           have i₂ := b0e33 X2 X0
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op y X1) := by
        intro X1 X2
        first
        | (have i₁ := b0e43 x X1 X2
           have i₂ := b0e44 x X1
           grind)
        | exact superpose b0e44 b0e43
        | exact resolve b0e43 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e44
      have b0e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
      have b0e78 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X1))) = X2 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X2 X1 (M.op X1 X1)
           have i₂ := b0e16 (M.op X1 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X1 X1) X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X1 X1) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e82 : ∀ X0 X1 X2 : G, (M.op y X0) = (k (M.op X1 X1) X0) ∨ (M.op X0 (M.op X2 (M.op X1 X1))) = X2 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e78 X0 X1 X2
           have i₂ := b0e49 X0 X1
           grind)
        | exact superpose b0e49 b0e78
        | (have j0 := b0e78 X0 X1 X2
           grind)
        | exact resolve b0e78 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e86 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X1))) = X2 ∨ (M.op y X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = (M.op y X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e82 X0 X1 X2
           have i₂ := b0e49 X0 X1
           grind)
        | exact superpose b0e49 b0e82
        | (have j0 := b0e82 X0 X1 X2
           grind)
        | exact resolve b0e82 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e82
      have b0e109 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e139 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = (M.op (σ y) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op (σ y) X2) X1 (M.op X0 X2)
           have i₂ := b0e34 X2 X0
           grind)
        | exact superpose b0e34 b0e11
        | exact resolve b0e11 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e140 : ∀ X2 : G, (M.op y X2) = (M.op (σ y) X2) := by
        intro X2
        first
        | (have i₁ := b0e139 x x X2
           have i₂ := b0e48 x x X2
           grind)
        | exact superpose b0e48 b0e139
        | exact resolve b0e139 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e139
      have b0e159 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X1 X1) X0) (M.op y X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X1 X0
           have i₂ := b0e140 X0
           grind)
        | exact superpose b0e140 b0e11
        | exact resolve b0e11 b0e140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e160 : y = (σ y) := by
        first
        | (have i₁ := b0e159 x x
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e159
        | exact resolve b0e159 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159
      have b0e193 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op y (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 X1 (M.op y (M.op X1 X1))
           have i₂ := b0e33 (M.op X1 X1) X0
           grind)
        | exact superpose b0e33 b0e36
        | exact resolve b0e36 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e200 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) X0) = X2 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X1 (M.op X0 (M.op X2 (M.op X3 X3)))
           have i₂ := b0e36 X2 X3 X0
           grind)
        | exact superpose b0e36 b0e11
        | exact resolve b0e11 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e208 : ∀ X2 X3 : G, (M.op y (M.op X2 (M.op X3 X3))) = X2 := by
        intro X2 X3
        first
        | (have i₁ := b0e200 x x X2 X3
           have i₂ := b0e48 x x (M.op X2 (M.op X3 X3))
           grind)
        | exact superpose b0e48 b0e200
        | exact resolve b0e200 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e200
      have b0e223 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e18
        | exact resolve b0e18 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e226 : y = (τ y) := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e12
        | exact resolve b0e12 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e313 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X4) = (M.op X2 (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X3 X3)))) X1)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e36 X2 X3 (M.op X4 X4)
           have i₂ := b0e39 X1 X0 (M.op X2 (M.op X3 X3)) X4
           grind)
        | (have i₁ := b0e36 X0 X1 (M.op (M.op X1 X1) (M.op (M.op X0 (M.op X1 X1)) X2))
           have i₂ := b0e39 (M.op X0 (M.op X1 X1)) X1 X2 X3
           grind)
        | exact superpose b0e39 b0e36
        | exact resolve b0e36 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e331 : ∀ X2 X3 X4 : G, (M.op X4 X4) = (M.op X2 (M.op y (M.op X2 (M.op X3 X3)))) := by
        intro X2 X3 X4
        first
        | (have i₁ := b0e313 x x X2 X3 X4
           have i₂ := b0e48 x x (M.op X2 (M.op X3 X3))
           grind)
        | exact superpose b0e48 b0e313
        | exact resolve b0e313 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e313
      have b0e389 : ∀ X4 : G, y = (M.op X4 X4) := by
        intro X4
        first
        | (have i₁ := b0e331 x x X4
           have i₂ := b0e36 x x y
           grind)
        | exact superpose b0e36 b0e331
        | exact resolve b0e331 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e331
      have b0e474 : ∀ X0 : G, (M.op (M.op y X0) y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33 X0 X0
           have i₂ := b0e389 X0
           grind)
        | exact superpose b0e389 b0e33
        | exact resolve b0e33 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e486 : ∀ X0 : G, (M.op y (M.op X0 y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e33 y X0
           have i₂ := b0e389 y
           grind)
        | exact superpose b0e389 b0e33
        | exact resolve b0e33 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e973 : ∀ X0 X1 : G, y = X0 ∨ (M.op y (M.op X0 (M.op X1 X1))) = (k (M.op X1 X1) (M.op X0 (M.op X1 X1))) ∨ (M.op X1 X1) = (M.op y (M.op X0 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e389 (M.op X0 (M.op X1 X1))
           have i₂ := b0e86 (M.op X0 (M.op X1 X1)) X1 X0
           grind)
        | exact superpose b0e86 b0e389
        | (have j1 := b0e86 (M.op X0 (M.op X1 X1)) X1 x
           grind)
        | exact resolve b0e389 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86
      have b0e998 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (k y (M.op X0 y)) ∨ y = X0 ∨ (M.op X1 X1) = (M.op y (M.op X0 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e973 X0 x
           have i₂ := b0e389 x
           grind)
        | exact superpose b0e389 b0e973
        | (have j0 := b0e973 X0 X1
           grind)
        | exact resolve b0e973 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e973
      have b0e1042 : ∀ X0 X1 : G, (k y (M.op X0 y)) = X0 ∨ y = X0 ∨ (M.op X1 X1) = (M.op y (M.op X0 (M.op X1 X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e998 X0 X1
           have i₂ := b0e486 X0
           grind)
        | exact superpose b0e486 b0e998
        | (have j0 := b0e998 X0 X1
           grind)
        | exact resolve b0e998 b0e486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e486 b0e998
      have b0e1086 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k y (M.op X0 y)) = X0 ∨ y = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e1042 X0 X1
           have i₂ := b0e208 X0 X1
           grind)
        | (have i₁ := b0e1042 X0 X1
           have i₂ := b0e208 (M.op y (M.op X0 (M.op X1 X1))) x
           grind)
        | exact superpose b0e208 b0e1042
        | (have j0 := b0e1042 X0 X1
           grind)
        | exact resolve b0e1042 b0e208
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e208 b0e1042
      have b0e1126 : ∀ X0 : G, y = X0 ∨ (k y (M.op X0 y)) = X0 ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e1086 X0 x
           have i₂ := b0e389 x
           grind)
        | exact superpose b0e389 b0e1086
        | (have j0 := b0e1086 X0 x
           grind)
        | exact resolve b0e1086 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1086
      have b0e1127 : ∀ X0 : G, (k y (M.op X0 y)) = X0 ∨ y = X0 := by
        intro X0
        first
        | (have j0 := b0e1126 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1126
      have b0e1869 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op y (σ X0)) ∨ (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e193 X1 (σ X2)
           have i₂ := b0e68 X2 X0
           grind)
        | exact superpose b0e68 b0e193
        | (have j1 := b0e68 X2 X0
           grind)
        | exact resolve b0e193 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68 b0e193
      have b0e1988 : ∀ X0 X2 : G, (σ (k X2 X0)) = (M.op (σ X2) (σ X0)) ∨ y = (M.op y (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e1869 X0 x X2
           have i₂ := b0e389 x
           grind)
        | exact superpose b0e389 b0e1869
        | (have j0 := b0e1869 X0 x X2
           grind)
        | exact resolve b0e1869 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1869
      have b0e2399 : ∀ X0 : G, (k y (τ X0)) = (τ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e109 y X0
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e109
        | exact resolve b0e109 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e109
      have b0e2880 : ∀ X0 : G, (τ X0) = (k y (τ (M.op X0 y))) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e2399 (M.op X0 y)
           have i₂ := b0e1127 X0
           grind)
        | exact superpose b0e1127 b0e2399
        | (have j1 := b0e1127 X0
           grind)
        | exact resolve b0e2399 b0e1127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1127 b0e2399
      have b0e345434 : ∀ X0 X1 : G, (M.op (σ (k y X0)) (M.op X1 (σ X0))) = X1 ∨ y = (M.op y (σ X0)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 (σ X0) X1
           have i₂ := b0e1988 X0 y
           grind)
        | exact superpose b0e1988 b0e34
        | (have j1 := b0e1988 X0 y
           grind)
        | exact resolve b0e34 b0e1988
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34 b0e1988
      have b0e345487 : ∀ X0 X1 : G, (σ y) = (M.op y (σ X0)) ∨ (M.op (σ (k y X0)) (M.op X1 (σ X0))) = X1 ∨ y = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e345434 X0 X1
           have i₂ := b0e140 (σ X0)
           grind)
        | exact superpose b0e140 b0e345434
        | (have j0 := b0e345434 X0 X1
           grind)
        | exact resolve b0e345434 b0e140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140 b0e345434
      have b0e345507 : ∀ X0 X1 : G, y = (M.op y (σ X0)) ∨ (M.op (σ (k y X0)) (M.op X1 (σ X0))) = X1 ∨ y = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e345487 X0 X1
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e345487
        | (have j0 := b0e345487 X0 X1
           grind)
        | exact resolve b0e345487 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345487
      have b0e345508 : ∀ X0 X1 : G, (M.op (σ (k y X0)) (M.op X1 (σ X0))) = X1 ∨ y = (M.op y (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e345507 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345507
      have b0e623553 : ∀ X0 X1 : G, (M.op (σ (k y (τ X0))) (M.op X1 X0)) = X1 ∨ y = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e345508 (τ X0) X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e345508
        | exact resolve b0e345508 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e345508
      have b0e623714 : ∀ X0 X1 : G, (M.op (k (σ y) X0) (M.op X1 X0)) = X1 ∨ y = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e623553 X0 X1
           have i₂ := b0e26 X0 y
           grind)
        | exact superpose b0e26 b0e623553
        | (have j0 := b0e623553 X0 X1
           grind)
        | exact resolve b0e623553 b0e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e623553
      have b0e623768 : ∀ X0 X1 : G, (M.op (k y X0) (M.op X1 X0)) = X1 ∨ y = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e623714 X0 X1
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e623714
        | (have j0 := b0e623714 X0 X1
           grind)
        | exact resolve b0e623714 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e623714
      have b0e623910 : ∀ X0 : G, (M.op (k y X0) y) = X0 ∨ y = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e623768 X0 X0
           have i₂ := b0e389 X0
           grind)
        | exact superpose b0e389 b0e623768
        | (have j0 := b0e623768 X0 x
           grind)
        | exact resolve b0e623768 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e623768
      have b0e624457 : ∀ X0 : G, y = (M.op y (τ (M.op X0 y))) ∨ (τ (M.op X0 y)) = (M.op (τ X0) y) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e623910 (τ (M.op X0 y))
           have i₂ := b0e2880 X0
           grind)
        | exact superpose b0e2880 b0e623910
        | (have j0 := b0e623910 (τ (M.op X0 y))
           have j1 := b0e2880 (M.op y (τ (M.op X0 y)))
           grind)
        | exact resolve b0e623910 b0e2880
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2880 b0e623910
      have b0e1106855 : ∀ X0 : G, (M.op y y) = (τ (M.op X0 y)) ∨ (τ (M.op X0 y)) = (M.op (τ X0) y) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e474 (τ (M.op X0 y))
           have i₂ := b0e624457 X0
           grind)
        | exact superpose b0e624457 b0e474
        | (have j1 := b0e624457 X0
           grind)
        | exact resolve b0e474 b0e624457
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e624457
      have b0e1106856 : ∀ X0 : G, (τ (M.op X0 y)) = (M.op (τ X0) y) ∨ y = (τ (M.op X0 y)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e1106855 X0
           have i₂ := b0e389 y
           grind)
        | exact superpose b0e389 b0e1106855
        | (have j0 := b0e1106855 X0
           grind)
        | exact resolve b0e1106855 b0e389
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e389 b0e1106855
      have b0e1106864 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) ∨ y = (τ (M.op X0 y)) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op X0 y)
           have i₂ := b0e1106856 X0
           grind)
        | exact superpose b0e1106856 b0e13
        | (have j1 := b0e1106856 X0
           grind)
        | exact resolve b0e13 b0e1106856
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1106856
      have b0e1106943 : ∀ X0 : G, y = (τ (M.op (σ X0) y)) ∨ (M.op (σ X0) y) = (σ (M.op X0 y)) ∨ (σ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e1106864 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1106864
        | (have j0 := b0e1106864 (σ X0)
           grind)
        | exact resolve b0e1106864 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1106864
      have b0e1150444 : ∀ X0 : G, (σ y) = (M.op (σ X0) y) ∨ (M.op (σ X0) y) = (σ (M.op X0 y)) ∨ (σ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op (σ X0) y)
           have i₂ := b0e1106943 X0
           grind)
        | exact superpose b0e1106943 b0e13
        | (have j1 := b0e1106943 X0
           grind)
        | exact resolve b0e13 b0e1106943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1106943
      have b0e1150445 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) ∨ y = (M.op (σ X0) y) ∨ (σ X0) = y := by
        intro X0
        first
        | (have i₁ := b0e1150444 X0
           have i₂ := b0e160
           grind)
        | exact superpose b0e160 b0e1150444
        | (have j0 := b0e1150444 X0
           grind)
        | exact resolve b0e1150444 b0e160
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e160 b0e1150444
      have b0e1150450 : (M.op (σ x) y) ≠ (M.op (σ x) y) ∨ y = (M.op (σ x) y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e223
           have i₂ := b0e1150445 x
           grind)
        | exact superpose b0e1150445 b0e223
        | (have j1 := b0e1150445 x
           grind)
        | (have r₁ := b0e223
           have r₂ := b0e1150445 x
           grind)
        | exact resolve b0e223 b0e1150445
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e223 b0e1150445
      have b0e1150452 : y = (M.op (σ x) y) ∨ y = (σ x) := by grind
      clear b0e1150450
      have b0e1150757 : (σ x) = (M.op (M.op y y) y) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e33 y (σ x)
           have i₂ := b0e1150452
           grind)
        | exact superpose b0e1150452 b0e33
        | exact resolve b0e33 b0e1150452
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e1150452
      have b0e1151044 : y = (σ x) ∨ y = (σ x) := by
        first
        | (have i₁ := b0e1150757
           have i₂ := b0e474 y
           grind)
        | exact superpose b0e474 b0e1150757
        | exact resolve b0e1150757 b0e474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e474 b0e1150757
      have b0e1151045 : y = (σ x) := by grind
      clear b0e1151044
      have b0e1151420 : x = (τ y) := by
        first
        | (have i₁ := b0e12 x
           have i₂ := b0e1151045
           grind)
        | exact superpose b0e1151045 b0e12
        | exact resolve b0e12 b0e1151045
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1151045
      have b0e1151877 : x = y := by
        first
        | (have i₁ := b0e226
           have i₂ := b0e1151420
           grind)
        | exact superpose b0e1151420 b0e226
        | exact resolve b0e226 b0e1151420
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e226 b0e1151420
      have b0e1153872 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1151877
           grind)
        | exact superpose b0e1151877 b0e18
        | exact resolve b0e18 b0e1151877
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1151877
      have b0e1157039 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e1153872
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e1153872
        | exact resolve b0e1153872 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1153872
      have b0e1157511 : False := by grind
      exact b0e1157511
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b1e28 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 x X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
             have i₂ := b1e12 X0 X1 (M.op X1 X1)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 y))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 y (M.op X0 y)
             have i₂ := b1e28 y X0
             grind)
          | exact superpose b1e28 b1e12
          | exact resolve b1e12 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e108 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b1e39 X0 (M.op y y)
             have i₂ := b1e28 y X0
             grind)
          | exact superpose b1e28 b1e39
          | exact resolve b1e39 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e134 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
          intro X0
          grind
        have b1e140 : y = (M.op y y) := by
          first
          | (have i₁ := b1e28 x y
             have i₂ := b1e108 (M.op y x)
             grind)
          | exact superpose b1e108 b1e28
          | exact resolve b1e28 b1e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e108
        have b1e157 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b1e134 X0
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e134
          | exact resolve b1e134 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e134 b1e140
        have b1e174 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b1e30 X0 y y
             have i₂ := b1e39 y X0
             grind)
          | exact superpose b1e39 b1e30
          | exact resolve b1e30 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e39
        have b1e218 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e174 (σ x)
             grind)
          | exact superpose b1e174 b1e21
          | exact resolve b1e21 b1e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e502 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e26 X0 y
             have i₂ := b1e157 (τ X0)
             grind)
          | exact superpose b1e157 b1e26
          | exact resolve b1e26 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e157
        have b1e505 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e502 X0
             have i₂ := b1e14 X0
             grind)
          | exact superpose b1e14 b1e502
          | exact resolve b1e502 b1e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e502
        have b1e528 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e17 X0 (σ y)
             have i₂ := b1e505 X0
             grind)
          | exact superpose b1e505 b1e17
          | (have j0 := b1e17 X0 (σ y)
             grind)
          | exact resolve b1e17 b1e505
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e505
        have b1e531 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have j0 := b1e528 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e528
        have b1e535 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b1e531 X0
             have i₂ := b1e174 X0
             grind)
          | exact superpose b1e174 b1e531
          | (have j0 := b1e531 X0
             grind)
          | exact resolve b1e531 b1e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e531
        have b1e537 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
          intro X0
          first
          | (have j0 := b1e535 X0
             grind)
          | (have r₁ := b1e535 X0
             have r₂ := b1e218
             grind)
          | exact resolve b1e535 b1e218
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e535
        have b1e680 : y = (σ y) := by
          first
          | (have i₁ := b1e174 (σ y)
             have i₂ := b1e537 (σ y)
             grind)
          | exact superpose b1e537 b1e174
          | exact resolve b1e174 b1e537
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e174 b1e537
        have b1e705 : False := by grind
        exact b1e705
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 y))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 y (M.op X0 y)
             have i₂ := b2e27 y X0
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
        have b2e100 : ∀ X0 : G, (M.op X0 X0) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b2e36 X0 (M.op y y)
             have i₂ := b2e27 y X0
             grind)
          | exact superpose b2e27 b2e36
          | exact resolve b2e36 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e127 : ∀ X0 : G, (k X0 (M.op y y)) = X0 := by
          intro X0
          grind
        have b2e133 : y = (M.op y y) := by
          first
          | (have i₁ := b2e27 x y
             have i₂ := b2e100 (M.op y x)
             grind)
          | exact superpose b2e100 b2e27
          | exact resolve b2e27 b2e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e100
        have b2e150 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b2e127 X0
             have i₂ := b2e133
             grind)
          | exact superpose b2e133 b2e127
          | exact resolve b2e127 b2e133
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e127 b2e133
        have b2e481 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e67 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e482 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e481
             have r₂ := b2e22
             grind)
          | exact resolve b2e481 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e481
        have b2e483 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e482
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e482
          | exact resolve b2e482 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e482
        have b2e484 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e483
             have i₂ := b2e150 x
             grind)
          | exact superpose b2e150 b2e483
          | exact resolve b2e483 b2e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e150 b2e483
        have b2e485 : False := by grind
        exact b2e485
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
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
        have b3e39 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e13 (k (τ X0) X1)
             have i₂ := b3e29 X0 X1
             grind)
          | exact superpose b3e29 b3e13
          | exact resolve b3e13 b3e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
             have i₂ := b3e12 X0 X1 (M.op X1 X1)
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e127 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e43 X1 (M.op X0 X0) (M.op X0 X0)
             have i₂ := b3e43 (M.op X0 X0) X0 X1
             grind)
          | exact superpose b3e43 b3e43
          | exact resolve b3e43 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e173 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = X1 := by
          intro X0 X1
          grind
        have b3e184 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e22
             have i₂ := b3e127 X0 (σ x)
             grind)
          | (have i₁ := b3e22
             have i₂ := b3e127 (σ x) X0
             grind)
          | exact superpose b3e127 b3e22
          | exact resolve b3e22 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e186 : ∀ X0 : G, (M.op X0 X0) ≠ y := by
          intro X0
          first
          | (have i₁ := b3e20
             have i₂ := b3e127 X0 x
             grind)
          | (have i₁ := b3e20
             have i₂ := b3e127 x X0
             grind)
          | exact superpose b3e127 b3e20
          | exact resolve b3e20 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127
        have b3e193 : ∀ X1 : G, (k X1 (σ y)) = X1 := by
          intro X1
          first
          | (have i₁ := b3e173 x X1
             have i₂ := b3e184 x
             grind)
          | exact superpose b3e184 b3e173
          | exact resolve b3e173 b3e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e173 b3e184
        have b3e497 : ∀ X0 : G, (τ X0) = (k (τ X0) y) := by
          intro X0
          first
          | (have i₁ := b3e39 X0 y
             have i₂ := b3e193 X0
             grind)
          | exact superpose b3e193 b3e39
          | exact resolve b3e39 b3e193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e193
        have b3e514 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e497 (σ X0)
             have i₂ := b3e13 X0
             grind)
          | exact superpose b3e13 b3e497
          | exact resolve b3e497 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e497
        have b3e645 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y ∨ (M.op X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e17 X0 y
             have i₂ := b3e514 X0
             grind)
          | exact superpose b3e514 b3e17
          | (have j0 := b3e17 X0 y
             grind)
          | exact resolve b3e17 b3e514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e514
        have b3e649 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y := by
          intro X0
          first
          | (have j0 := b3e645 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e645
        have b3e657 : ∀ X0 : G, (M.op X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e649 X0
             grind)
          | (have r₁ := b3e649 y
             have r₂ := b3e186 y
             grind)
          | (have r₁ := b3e649 X0
             have r₂ := b3e186 X0
             grind)
          | exact resolve b3e649 b3e186
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e649
        have b3e862 : y ≠ y := by
          first
          | (have i₁ := b3e186 y
             have i₂ := b3e657 y
             grind)
          | exact superpose b3e657 b3e186
          | (have r₁ := b3e186 y
             have r₂ := b3e657 y
             grind)
          | exact resolve b3e186 b3e657
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e186 b3e657
        have b3e879 : False := by grind
        exact b3e879
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b5e42 : x ≠ x ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e45 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e42
          have b5e48 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) X0) := by
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
          have b5e244 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e245 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e244
               have r₂ := b5e24
               grind)
            | exact resolve b5e244 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244
          have b5e246 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e245
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e245
            | exact resolve b5e245 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245
          have b5e247 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e246
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e246
            | exact resolve b5e246 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e246
          have b5e248 : False := by grind
          exact b5e248
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
        have b6e76 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e88 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e76
        have b6e94 : y = (M.op x x) := by
          first
          | (have r₁ := b6e88
             have r₂ := b6e21
             grind)
          | exact resolve b6e88 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e100 : False := by grind
        exact b6e100
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e40
          have b7e44 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e45 : (σ x) = (σ (k x y)) := by
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
          have b7e57 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e45
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e45
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e45 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e65 : y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e57
               have r₂ := b7e26
               grind)
            | exact resolve b7e57 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e57
          have b7e66 : x = (M.op x y) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e21
               grind)
            | exact resolve b7e65 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : False := by grind
          exact b7e67
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
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
          have b8e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e442 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e52 x y
               grind)
            | exact superpose b8e52 b8e20
            | (have j1 := b8e52 x y
               grind)
            | exact resolve b8e20 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e526 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e442
               have r₂ := b8e23
               grind)
            | exact resolve b8e442 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e442
          have b8e534 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e526
               have r₂ := b8e24
               grind)
            | exact resolve b8e526 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e526
          have b8e537 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e534
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e534
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e534 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e534
          have b8e538 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e537
          have b8e540 : x = (M.op x y) := by
            first
            | (have r₁ := b8e538
               have r₂ := b8e21
               grind)
            | exact resolve b8e538 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e538
          have b8e542 : False := by grind
          exact b8e542

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_x_pyx_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (x) (y) with h0a | h0a
  · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (y) (x) with h2a | h2a
      · have b0e15 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          grind
        have b0e32 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          grind
        clear b0e31
        have b0e79 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
        clear b0e32
        have b0e84 : False := by grind
        exact b0e84
      · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
        · have b1e21 : x = y := by grind
          have b1e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e31 : False := by grind
          exact b1e31
        · have b2e21 : x = y := by grind
          have b2e23 : x ≠ y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e31 : False := by grind
          exact b2e31
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b3e21 : x = y := by grind
          have b3e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e31 : False := by grind
          exact b3e31
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b4e22 : x = y := by grind
            have b4e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e34 : False := by grind
            exact b4e34
          · have b5e22 : x = y := by grind
            have b5e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e34 : False := by grind
            exact b5e34
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b6e21 : x = y := by grind
          have b6e22 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e31 : False := by grind
          exact b6e31
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b7e22 : x = y := by grind
            have b7e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e34 : False := by grind
            exact b7e34
          · have b8e22 : x = y := by grind
            have b8e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e34 : False := by grind
            exact b8e34
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b9e21 : x ≠ y := by grind
          have b9e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e31 : False := by grind
          exact b9e31
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e24 : (σ x) = (σ y) := by grind
            have b10e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b10e15 y
                 have i₂ := b10e24
                 grind)
              | exact superpose b10e24 b10e15
              | exact resolve b10e15 b10e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b10e31 : x = y := by
              first
              | (have i₁ := b10e30
                 have i₂ := b10e15 x
                 grind)
              | exact superpose b10e15 b10e30
              | exact resolve b10e30 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e30
            have b10e32 : False := by grind
            exact b10e32
          · have b11e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b11e24 : (σ x) = (σ y) := by grind
            have b11e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b11e15 y
                 have i₂ := b11e24
                 grind)
              | exact superpose b11e24 b11e15
              | exact resolve b11e15 b11e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b11e31 : x = y := by
              first
              | (have i₁ := b11e30
                 have i₂ := b11e15 x
                 grind)
              | exact superpose b11e15 b11e30
              | exact resolve b11e30 b11e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b11e30
            have b11e32 : False := by grind
            exact b11e32
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b12e24 : (σ x) ≠ (σ y) := by grind
            have b12e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e34 : False := by grind
            exact b12e34
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b13e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b13e24 : y = (M.op x x) := by grind
              have b13e27 : x ≠ y := by grind
              have b13e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e46 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X1 x X0
                   have i₂ := b13e24
                   grind)
                | exact superpose b13e24 b13e15
                | exact resolve b13e15 b13e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e47 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b13e15 X1 y X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e15
                | exact resolve b13e15 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b13e53 : ∀ X0 : G, (M.op x (M.op X0 y)) = X0 := by
                intro X0
                first
                | (have i₁ := b13e46 y X0
                   have i₂ := b13e28
                   grind)
                | exact superpose b13e28 b13e46
                | exact resolve b13e46 b13e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e46
              have b13e125 : ∀ X0 : G, (M.op X0 X0) = x := by
                intro X0
                first
                | (have i₁ := b13e47 (M.op X0 y) x
                   have i₂ := b13e53 X0
                   grind)
                | exact superpose b13e53 b13e47
                | exact resolve b13e47 b13e53
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e47 b13e53
              have b13e167 : x = y := by
                first
                | (have i₁ := b13e24
                   have i₂ := b13e125 x
                   grind)
                | exact superpose b13e125 b13e24
                | exact resolve b13e24 b13e125
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b13e125
              have b13e170 : False := by grind
              exact b13e170
            · have b14e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b14e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b14e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b14e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b14e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b14e24 : y = (M.op x x) := by grind
              have b14e25 : (σ x) ≠ (σ y) := by grind
              have b14e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b14e27 : x ≠ y := by grind
              have b14e28 : x ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b14e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b14e34
              have b14e44 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b14e15 X1 x X0
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e15 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
                   have i₂ := b14e15 X0 X1 (M.op X1 X1)
                   grind)
                | exact superpose b14e15 b14e15
                | exact resolve b14e15 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e48 : ∀ X0 : G, x = (M.op (M.op (M.op X0 X0) x) y) := by
                intro X0
                first
                | (have i₁ := b14e15 x X0 x
                   have i₂ := b14e24
                   grind)
                | exact superpose b14e24 b14e15
                | exact resolve b14e15 b14e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op y (M.op X0 X1)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b14e44 (M.op X0 X1) (M.op (M.op X2 X2) X1)
                   have i₂ := b14e15 X0 X2 X1
                   grind)
                | exact superpose b14e15 b14e44
                | exact resolve b14e44 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e54 : ∀ X0 X1 : G, (M.op (M.op y (M.op X0 X1)) X0) = (M.op y X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e44 (M.op X0 X1) (M.op y X1)
                   have i₂ := b14e44 X1 X0
                   grind)
                | exact superpose b14e44 b14e44
                | exact resolve b14e44 b14e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e58 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op y X1) := by
                intro X1 X2
                first
                | (have i₁ := b14e53 x X1 X2
                   have i₂ := b14e54 x X1
                   grind)
                | exact superpose b14e54 b14e53
                | exact resolve b14e53 b14e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e53 b14e54
              have b14e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e21 X1 X0
                   have i₂ := b14e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b14e20 b14e21
                | (have j1 := b14e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b14e21 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b14e77 X0 X1
                   have i₂ := b14e35 X1
                   grind)
                | exact superpose b14e35 b14e77
                | (have j0 := b14e77 X0 X1
                   grind)
                | exact resolve b14e77 b14e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e77
              have b14e103 : x = (M.op (M.op (σ y) x) y) := by
                first
                | (have i₁ := b14e48 (σ x)
                   have i₂ := b14e26
                   grind)
                | exact superpose b14e26 b14e48
                | exact resolve b14e48 b14e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e48
              have b14e110 : (M.op (M.op y y) x) = (M.op (σ y) x) := by
                first
                | (have i₁ := b14e44 y (M.op (σ y) x)
                   have i₂ := b14e103
                   grind)
                | exact superpose b14e103 b14e44
                | exact resolve b14e44 b14e103
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e44 b14e103
              have b14e113 : (M.op y x) = (M.op (σ y) x) := by
                first
                | (have i₁ := b14e110
                   have i₂ := b14e58 x y
                   grind)
                | exact superpose b14e58 b14e110
                | exact resolve b14e110 b14e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e58 b14e110
              have b14e129 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) x) (M.op y x)) := by
                intro X0
                first
                | (have i₁ := b14e15 (σ y) X0 x
                   have i₂ := b14e113
                   grind)
                | exact superpose b14e113 b14e15
                | exact resolve b14e15 b14e113
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e113
              have b14e130 : y = (σ y) := by
                first
                | (have i₁ := b14e129 x
                   have i₂ := b14e15 y x x
                   grind)
                | exact superpose b14e15 b14e129
                | exact resolve b14e129 b14e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e129
              have b14e148 : y ≠ (σ x) := by
                first
                | (have i₁ := b14e25
                   have i₂ := b14e130
                   grind)
                | exact superpose b14e130 b14e25
                | exact resolve b14e25 b14e130
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b14e149 : (M.op y y) = (σ (M.op y y)) := by
                first
                | (have i₁ := b14e35 y
                   have i₂ := b14e130
                   grind)
                | exact superpose b14e130 b14e35
                | exact resolve b14e35 b14e130
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e35 b14e130
              have b14e216 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
                intro X0 X1
                first
                | (have i₁ := b14e47 X1 (M.op X0 X0) (M.op X0 X0)
                   have i₂ := b14e47 (M.op X0 X0) X0 X1
                   grind)
                | exact superpose b14e47 b14e47
                | exact resolve b14e47 b14e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e47
              have b14e320 : ∀ X0 : G, (M.op X0 X0) = y := by
                intro X0
                first
                | (have i₁ := b14e24
                   have i₂ := b14e216 X0 x
                   grind)
                | (have i₁ := b14e24
                   have i₂ := b14e216 x X0
                   grind)
                | exact superpose b14e216 b14e24
                | exact resolve b14e24 b14e216
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e216
              have b14e1131 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b14e22
                   have i₂ := b14e92 x y
                   grind)
                | exact superpose b14e92 b14e22
                | (have j1 := b14e92 x y
                   grind)
                | exact resolve b14e22 b14e92
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e92
              have b14e1171 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
                first
                | (have r₁ := b14e1131
                   have r₂ := b14e25
                   grind)
                | exact resolve b14e1131 b14e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1131
              have b14e1221 : (σ x) = (M.op y y) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have i₁ := b14e1171
                   have i₂ := b14e149
                   grind)
                | exact superpose b14e149 b14e1171
                | exact resolve b14e1171 b14e149
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e149 b14e1171
              have b14e1256 : y = (σ x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have i₁ := b14e1221
                   have i₂ := b14e320 y
                   grind)
                | exact superpose b14e320 b14e1221
                | exact resolve b14e1221 b14e320
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e320 b14e1221
              have b14e1271 : (σ (M.op x y)) ≠ (σ (k y x)) := by
                first
                | (have r₁ := b14e1256
                   have r₂ := b14e148
                   grind)
                | exact resolve b14e1256 b14e148
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e148 b14e1256
              have b14e1991 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = y := by
                first
                | (have i₁ := b14e1271
                   have i₂ := b14e20 y x
                   grind)
                | exact superpose b14e20 b14e1271
                | (have j1 := b14e20 y x
                   grind)
                | (have r₁ := b14e1271
                   have r₂ := b14e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b14e1271
                   have r₂ := b14e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b14e1271 b14e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1271
              have b14e1993 : x = (M.op y y) ∨ x = y := by grind
              clear b14e1991
              have b14e1998 : x = y := by
                first
                | (have r₁ := b14e1993
                   have r₂ := b14e28
                   grind)
                | exact resolve b14e1993 b14e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b14e1993
              have b14e2003 : False := by grind
              exact b14e2003
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b15e24 : (σ x) ≠ (σ y) := by grind
            have b15e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e34 : False := by grind
            exact b15e34
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b16e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b16e24 : y = (M.op x x) := by grind
              have b16e27 : x ≠ y := by grind
              have b16e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e44 : ∀ X0 X1 : G, (M.op (M.op y X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X1 x X0
                   have i₂ := b16e24
                   grind)
                | exact superpose b16e24 b16e15
                | exact resolve b16e15 b16e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e45 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b16e15 X1 y X0
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e15
                | exact resolve b16e15 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b16e51 : ∀ X0 : G, (M.op x (M.op X0 y)) = X0 := by
                intro X0
                first
                | (have i₁ := b16e44 y X0
                   have i₂ := b16e28
                   grind)
                | exact superpose b16e28 b16e44
                | exact resolve b16e44 b16e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e44
              have b16e117 : ∀ X0 : G, (M.op X0 X0) = x := by
                intro X0
                first
                | (have i₁ := b16e45 (M.op X0 y) x
                   have i₂ := b16e51 X0
                   grind)
                | exact superpose b16e51 b16e45
                | exact resolve b16e45 b16e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e45 b16e51
              have b16e157 : x = y := by
                first
                | (have i₁ := b16e24
                   have i₂ := b16e117 x
                   grind)
                | exact superpose b16e117 b16e24
                | exact resolve b16e24 b16e117
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b16e117
              have b16e160 : False := by grind
              exact b16e160
            · have b17e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b17e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b17e24 : y = (M.op x x) := by grind
              have b17e26 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b17e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b17e34
              have b17e167 : (σ y) ≠ (σ (M.op x x)) := by
                first
                | (have i₁ := b17e26
                   have i₂ := b17e35 x
                   grind)
                | exact superpose b17e35 b17e26
                | exact resolve b17e26 b17e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e35
              have b17e178 : (σ y) ≠ (σ y) := by
                first
                | (have i₁ := b17e167
                   have i₂ := b17e24
                   grind)
                | exact superpose b17e24 b17e167
                | exact resolve b17e167 b17e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b17e167
              have b17e179 : False := by grind
              exact b17e179
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (y) (x) with h2a | h2a
        · have b18e21 : x ≠ y := by grind
          have b18e24 : x = y := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e31 : False := by grind
          exact b18e31
        · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
          · have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e24 : (σ x) = (σ y) := by grind
            have b19e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e15
              | exact resolve b19e15 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e31 : x = y := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e30
              | exact resolve b19e30 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e32 : False := by grind
            exact b19e32
          · have b20e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b20e24 : (σ x) = (σ y) := by grind
            have b20e25 : x ≠ y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b20e15 y
                 have i₂ := b20e24
                 grind)
              | exact superpose b20e24 b20e15
              | exact resolve b20e15 b20e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b20e31 : x = y := by
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
            have b20e32 : False := by grind
            exact b20e32
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b21e24 : (σ x) ≠ (σ y) := by grind
            have b21e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e34 : False := by grind
            exact b21e34
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b22e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e19 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
                intro X0 X1
                grind
              have b22e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b22e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b22e24 : y ≠ (M.op x x) := by grind
              have b22e25 : (σ x) ≠ (σ y) := by grind
              have b22e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              have b22e27 : x ≠ y := by grind
              have b22e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e44 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b22e15 X1 y X0
                   have i₂ := b22e28
                   grind)
                | exact superpose b22e28 b22e15
                | exact resolve b22e15 b22e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e53 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op x (M.op X0 X1)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b22e44 (M.op X0 X1) (M.op (M.op X2 X2) X1)
                   have i₂ := b22e15 X0 X2 X1
                   grind)
                | exact superpose b22e15 b22e44
                | exact resolve b22e44 b22e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e54 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b22e44 (M.op X0 X1) (M.op x X1)
                   have i₂ := b22e44 X1 X0
                   grind)
                | exact superpose b22e44 b22e44
                | exact resolve b22e44 b22e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e58 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op x X1) := by
                intro X1 X2
                first
                | (have i₁ := b22e53 x X1 X2
                   have i₂ := b22e54 x X1
                   grind)
                | exact superpose b22e54 b22e53
                | exact resolve b22e53 b22e54
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e53 b22e54
              have b22e60 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
              have b22e66 : (σ x) = (k (σ x) (σ y)) := by
                first
                | (have r₁ := b22e60
                   have r₂ := b22e25
                   grind)
                | exact resolve b22e60 b22e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e60
              have b22e70 : (σ x) = (σ (k x y)) := by
                first
                | (have i₁ := b22e66
                   have i₂ := b22e21 x y
                   grind)
                | exact superpose b22e21 b22e66
                | exact resolve b22e66 b22e21
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e66
              have b22e100 : (k x y) = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 (k x y)
                   have i₂ := b22e70
                   grind)
                | exact superpose b22e70 b22e16
                | exact resolve b22e16 b22e70
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e70
              have b22e101 : x = (k x y) := by
                first
                | (have i₁ := b22e100
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e100
                | exact resolve b22e100 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e100
              have b22e117 : x = (M.op y x) ∨ y = (M.op x x) ∨ x = y := by
                first
                | (have i₁ := b22e20 x y
                   have i₂ := b22e101
                   grind)
                | exact superpose b22e101 b22e20
                | (have j0 := b22e20 x y
                   grind)
                | exact resolve b22e20 b22e101
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e101
              have b22e118 : x = (M.op y x) ∨ x = y := by
                first
                | (have r₁ := b22e117
                   have r₂ := b22e24
                   grind)
                | exact resolve b22e117 b22e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e117
              have b22e120 : x = (M.op y x) := by
                first
                | (have r₁ := b22e118
                   have r₂ := b22e27
                   grind)
                | exact resolve b22e118 b22e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e118
              have b22e134 : y = (M.op (M.op x x) x) := by
                first
                | (have i₁ := b22e44 x y
                   have i₂ := b22e120
                   grind)
                | exact superpose b22e120 b22e44
                | exact resolve b22e44 b22e120
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e44 b22e120
              have b22e137 : y = (M.op x x) := by
                first
                | (have i₁ := b22e134
                   have i₂ := b22e58 x x
                   grind)
                | exact superpose b22e58 b22e134
                | exact resolve b22e134 b22e58
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e58 b22e134
              have b22e139 : False := by grind
              exact b22e139
            · have b23e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b23e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b23e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b23e24 : y ≠ (M.op x x) := by grind
              have b23e26 : (σ y) = (M.op (σ x) (σ x)) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b23e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b23e34
              have b23e105 : (σ y) = (σ (M.op x x)) := by
                first
                | (have i₁ := b23e26
                   have i₂ := b23e35 x
                   grind)
                | exact superpose b23e35 b23e26
                | exact resolve b23e26 b23e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e35
              have b23e161 : (M.op x x) = (τ (σ y)) := by
                first
                | (have i₁ := b23e16 (M.op x x)
                   have i₂ := b23e105
                   grind)
                | exact superpose b23e105 b23e16
                | exact resolve b23e16 b23e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e105
              have b23e162 : y = (M.op x x) := by
                first
                | (have i₁ := b23e161
                   have i₂ := b23e16 y
                   grind)
                | exact superpose b23e16 b23e161
                | exact resolve b23e161 b23e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b23e161
              have b23e166 : False := by grind
              exact b23e166
        · rcases eq_or_ne (y) (x) with h2a | h2a
          · have b24e24 : (σ x) ≠ (σ y) := by grind
            have b24e26 : x = y := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e34 : False := by grind
            exact b24e34
          · rcases eq_or_ne (M.op y y) (x) with h2b | h2b
            · have b25e15 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
                intro X0 X1 X2
                grind
              have b25e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b25e17 : ∀ X0 : G, (σ (τ X0)) = X0 := by
                intro X0
                grind
              have b25e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e24 : y ≠ (M.op x x) := by grind
              have b25e28 : x = (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 (τ X0) X1
                   have i₂ := b25e17 X0
                   grind)
                | exact superpose b25e17 b25e21
                | exact resolve b25e21 b25e17
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b25e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b25e34
              have b25e44 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 X0)) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 y X0
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e46 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e15 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
                   have i₂ := b25e15 X0 X1 (M.op X1 X1)
                   grind)
                | exact superpose b25e15 b25e15
                | exact resolve b25e15 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e47 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) x) := by
                intro X0
                first
                | (have i₁ := b25e15 y X0 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e15
                | exact resolve b25e15 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e50 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op x (M.op X0 X1)) X0) := by
                intro X0 X1 X2
                first
                | (have i₁ := b25e44 (M.op X0 X1) (M.op (M.op X2 X2) X1)
                   have i₂ := b25e15 X0 X2 X1
                   grind)
                | exact superpose b25e15 b25e44
                | exact resolve b25e44 b25e15
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e51 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = (M.op x X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e44 (M.op X0 X1) (M.op x X1)
                   have i₂ := b25e44 X1 X0
                   grind)
                | exact superpose b25e44 b25e44
                | exact resolve b25e44 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e52 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op X0 x))) = X1 := by
                intro X0 X1
                first
                | (have i₁ := b25e15 X1 x (M.op X0 x)
                   have i₂ := b25e44 x X0
                   grind)
                | exact superpose b25e44 b25e15
                | exact resolve b25e15 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e55 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op x X1) := by
                intro X1 X2
                first
                | (have i₁ := b25e50 x X1 X2
                   have i₂ := b25e51 x X1
                   grind)
                | exact superpose b25e51 b25e50
                | exact resolve b25e50 b25e51
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e50 b25e51
              have b25e70 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 X1 X0
                   have i₂ := b25e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b25e20 b25e21
                | (have j1 := b25e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b25e21 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e71 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (τ X1) = X0 := by
                intro X0 X1
                first
                | (have i₁ := b25e31 X1 X0
                   have i₂ := b25e20 (τ X1) X0
                   grind)
                | exact superpose b25e20 b25e31
                | (have j1 := b25e20 (τ X1) X0
                   grind)
                | exact resolve b25e31 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e31
              have b25e85 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e70 X0 X1
                   have i₂ := b25e35 X1
                   grind)
                | exact superpose b25e35 b25e70
                | (have j0 := b25e70 X0 X1
                   grind)
                | exact resolve b25e70 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e70
              have b25e105 : ∀ X0 : G, (M.op X0 X0) = (M.op x x) := by
                intro X0
                first
                | (have i₁ := b25e52 X0 (M.op x x)
                   have i₂ := b25e44 x X0
                   grind)
                | exact superpose b25e44 b25e52
                | exact resolve b25e52 b25e44
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e136 : ∀ X0 : G, (M.op (M.op x X0) (M.op x x)) = X0 := by
                intro X0
                first
                | (have i₁ := b25e44 X0 X0
                   have i₂ := b25e105 X0
                   grind)
                | (have i₁ := b25e44 x x
                   have i₂ := b25e105 X0
                   grind)
                | exact superpose b25e105 b25e44
                | exact resolve b25e44 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e143 : x = (M.op x x) := by
                first
                | (have i₁ := b25e28
                   have i₂ := b25e105 y
                   grind)
                | exact superpose b25e105 b25e28
                | exact resolve b25e28 b25e105
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e158 : ∀ X0 : G, (M.op (M.op x X0) x) = X0 := by
                intro X0
                first
                | (have i₁ := b25e136 X0
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e136
                | exact resolve b25e136 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e136
              have b25e171 : ∀ X0 : G, (M.op x x) = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e105 (σ X0)
                   have i₂ := b25e35 X0
                   grind)
                | exact superpose b25e35 b25e105
                | exact resolve b25e105 b25e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e35 b25e105
              have b25e180 : ∀ X0 : G, x = (σ (M.op X0 X0)) := by
                intro X0
                first
                | (have i₁ := b25e171 X0
                   have i₂ := b25e143
                   grind)
                | exact superpose b25e143 b25e171
                | exact resolve b25e171 b25e143
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e143 b25e171
              have b25e200 : ∀ X0 : G, (M.op X0 X0) = x := by
                intro X0
                first
                | (have i₁ := b25e46 X0 x x
                   have i₂ := b25e52 x X0
                   grind)
                | exact superpose b25e52 b25e46
                | exact resolve b25e46 b25e52
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e46 b25e52
              have b25e513 : x = (σ x) := by
                first
                | (have i₁ := b25e180 y
                   have i₂ := b25e28
                   grind)
                | exact superpose b25e28 b25e180
                | exact resolve b25e180 b25e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e516 : ∀ X0 X1 : G, (σ (k (M.op X0 X0) X1)) = (k x (σ X1)) := by
                intro X0 X1
                first
                | (have i₁ := b25e21 (M.op X0 X0) X1
                   have i₂ := b25e180 X0
                   grind)
                | exact superpose b25e180 b25e21
                | exact resolve b25e21 b25e180
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e517 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
                intro X0
                first
                | (have i₁ := b25e16 (M.op X0 X0)
                   have i₂ := b25e180 X0
                   grind)
                | exact superpose b25e180 b25e16
                | exact resolve b25e16 b25e180
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e518 : x = (τ x) := by
                first
                | (have i₁ := b25e517 x
                   have i₂ := b25e200 x
                   grind)
                | exact superpose b25e200 b25e517
                | exact resolve b25e517 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e517
              have b25e519 : ∀ X1 : G, (k x (σ X1)) = (σ (k x X1)) := by
                intro X1
                first
                | (have i₁ := b25e516 x X1
                   have i₂ := b25e200 x
                   grind)
                | exact superpose b25e200 b25e516
                | exact resolve b25e516 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e516
              have b25e529 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e513
                   grind)
                | exact superpose b25e513 b25e22
                | exact resolve b25e22 b25e513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b25e977 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op x (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e44 (σ X0) (σ X1)
                   have i₂ := b25e85 X1 X0
                   grind)
                | exact superpose b25e85 b25e44
                | (have j1 := b25e85 X1 X0
                   grind)
                | exact resolve b25e44 b25e85
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e44 b25e85
              have b25e1006 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op x (σ X0)) (σ (k X0 X1))) ∨ (σ X1) = x ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b25e977 X0 X1
                   have i₂ := b25e180 X0
                   grind)
                | exact superpose b25e180 b25e977
                | (have j0 := b25e977 X0 X1
                   grind)
                | exact resolve b25e977 b25e180
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e180 b25e977
              have b25e5939 : ∀ X0 : G, (M.op x x) = X0 ∨ (k x (σ X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e71 X0 x
                   have i₂ := b25e518
                   grind)
                | exact superpose b25e518 b25e71
                | exact resolve b25e71 b25e518
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e71
              have b25e6071 : ∀ X0 : G, x = X0 ∨ (k x (σ X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e5939 X0
                   have i₂ := b25e200 x
                   grind)
                | exact superpose b25e200 b25e5939
                | (have j0 := b25e5939 X0
                   grind)
                | exact resolve b25e5939 b25e200
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e200 b25e5939
              have b25e6072 : ∀ X0 : G, x = X0 ∨ (k x (σ X0)) = (σ (M.op X0 x)) := by
                intro X0
                first
                | (have j0 := b25e6071 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6071
              have b25e6133 : ∀ X0 : G, (σ (k x X0)) = (σ (M.op X0 x)) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e6072 X0
                   have i₂ := b25e519 X0
                   grind)
                | exact superpose b25e519 b25e6072
                | (have j0 := b25e6072 X0
                   grind)
                | exact resolve b25e6072 b25e519
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e519 b25e6072
              have b25e6960 : ∀ X0 : G, (σ X0) = (M.op (M.op x (σ x)) (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e1006 x X0
                   have i₂ := b25e6133 X0
                   grind)
                | exact superpose b25e6133 b25e1006
                | (have j0 := b25e1006 x X0
                   have j1 := b25e6133 (σ X0)
                   grind)
                | exact resolve b25e1006 b25e6133
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1006 b25e6133
              have b25e6996 : ∀ X0 : G, (σ X0) = (M.op (M.op x x) (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e6960 X0
                   have i₂ := b25e513
                   grind)
                | exact superpose b25e513 b25e6960
                | (have j0 := b25e6960 X0
                   grind)
                | exact resolve b25e6960 b25e513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6960
              have b25e7026 : ∀ X0 : G, (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e6996 X0
                   have i₂ := b25e55 (σ (M.op X0 x)) x
                   grind)
                | exact superpose b25e55 b25e6996
                | (have j0 := b25e6996 X0
                   grind)
                | exact resolve b25e6996 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e6996
              have b25e7041 : ∀ X0 : G, (σ X0) = x ∨ (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ x = X0 := by
                intro X0
                first
                | (have i₁ := b25e7026 X0
                   have i₂ := b25e513
                   grind)
                | exact superpose b25e513 b25e7026
                | (have j0 := b25e7026 X0
                   grind)
                | exact resolve b25e7026 b25e513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e513 b25e7026
              have b25e7042 : ∀ X0 : G, (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ x = X0 := by
                intro X0
                first
                | (have j0 := b25e7041 X0
                   grind)
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e7041
              have b25e213382 : ∀ X0 : G, (M.op x (σ y)) = (σ (M.op (M.op X0 X0) y)) ∨ x = (σ (M.op (M.op X0 X0) y)) ∨ x = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b25e7042 (M.op (M.op X0 X0) y)
                   have i₂ := b25e47 X0
                   grind)
                | exact superpose b25e47 b25e7042
                | (have j0 := b25e7042 (M.op (M.op X0 X0) y)
                   grind)
                | exact resolve b25e7042 b25e47
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e47 b25e7042
              have b25e213492 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (σ (M.op (M.op X0 X0) y)) ∨ x = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b25e213382 X0
                   have i₂ := b25e55 y X0
                   grind)
                | exact superpose b25e55 b25e213382
                | (have j0 := b25e213382 X0
                   grind)
                | exact resolve b25e213382 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e213382
              have b25e213506 : ∀ X0 : G, x = (σ (M.op (M.op X0 X0) y)) ∨ x = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have j0 := b25e213492 X0
                   grind)
                | (have r₁ := b25e213492 X0
                   have r₂ := b25e529
                   grind)
                | exact resolve b25e213492 b25e529
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e529 b25e213492
              have b25e213512 : ∀ X0 : G, x = (σ (M.op x y)) ∨ x = (M.op (M.op X0 X0) y) := by
                intro X0
                first
                | (have i₁ := b25e213506 X0
                   have i₂ := b25e55 y X0
                   grind)
                | exact superpose b25e55 b25e213506
                | (have j0 := b25e213506 X0
                   grind)
                | exact resolve b25e213506 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e213506
              have b25e213513 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e213512 x
                   have i₂ := b25e55 y x
                   grind)
                | exact superpose b25e55 b25e213512
                | exact resolve b25e213512 b25e55
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e55 b25e213512
              have b25e214110 : (M.op x y) = (τ x) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e16 (M.op x y)
                   have i₂ := b25e213513
                   grind)
                | exact superpose b25e213513 b25e16
                | exact resolve b25e16 b25e213513
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e213513
              have b25e214201 : x = (M.op x y) ∨ x = (M.op x y) := by
                first
                | (have i₁ := b25e214110
                   have i₂ := b25e518
                   grind)
                | exact superpose b25e518 b25e214110
                | exact resolve b25e214110 b25e518
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e518 b25e214110
              have b25e214202 : x = (M.op x y) := by grind
              clear b25e214201
              have b25e214915 : y = (M.op x x) := by
                first
                | (have i₁ := b25e158 y
                   have i₂ := b25e214202
                   grind)
                | exact superpose b25e214202 b25e158
                | exact resolve b25e158 b25e214202
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e158 b25e214202
              have b25e215095 : False := by grind
              exact b25e215095
            · have b26e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b26e18 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b26e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
                intro X0 X1
                grind
              have b26e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b26e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b26e25 : (σ x) ≠ (σ y) := by grind
              have b26e27 : x ≠ y := by grind
              have b26e28 : x ≠ (M.op y y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e34 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
                intro X0
                grind
              have b26e35 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
                intro X0
                grind
              clear b26e34
              have b26e75 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e21 X1 X0
                   have i₂ := b26e20 (σ X1) (σ X0)
                   grind)
                | exact superpose b26e20 b26e21
                | (have j1 := b26e20 (σ X1) (σ X0)
                   grind)
                | exact resolve b26e21 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b26e86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
                intro X0 X1
                first
                | (have i₁ := b26e75 X0 X1
                   have i₂ := b26e35 X1
                   grind)
                | exact superpose b26e35 b26e75
                | (have j0 := b26e75 X0 X1
                   grind)
                | exact resolve b26e75 b26e35
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e35 b26e75
              have b26e408 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b26e22
                   have i₂ := b26e86 x y
                   grind)
                | exact superpose b26e86 b26e22
                | (have j1 := b26e86 x y
                   grind)
                | exact resolve b26e22 b26e86
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e86
              have b26e441 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
                first
                | (have r₁ := b26e408
                   have r₂ := b26e25
                   grind)
                | exact resolve b26e408 b26e25
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e408
              have b26e4294 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
                first
                | (have i₁ := b26e441
                   have i₂ := b26e20 y x
                   grind)
                | exact superpose b26e20 b26e441
                | (have j1 := b26e20 y x
                   grind)
                | (have r₁ := b26e441
                   have r₂ := b26e20 (σ (M.op x y)) (σ (k y x))
                   grind)
                | (have r₁ := b26e441
                   have r₂ := b26e20 (σ (k y x)) (σ (M.op x y))
                   grind)
                | exact resolve b26e441 b26e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e441
              have b26e4296 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
              clear b26e4294
              have b26e4300 : (σ x) = (σ (M.op y y)) ∨ x = y := by
                first
                | (have r₁ := b26e4296
                   have r₂ := b26e28
                   grind)
                | exact resolve b26e4296 b26e28
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4296
              have b26e4304 : (σ x) = (σ (M.op y y)) := by
                first
                | (have r₁ := b26e4300
                   have r₂ := b26e27
                   grind)
                | exact resolve b26e4300 b26e27
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4300
              have b26e4332 : (M.op y y) = (τ (σ x)) := by
                first
                | (have i₁ := b26e16 (M.op y y)
                   have i₂ := b26e4304
                   grind)
                | exact superpose b26e4304 b26e16
                | exact resolve b26e16 b26e4304
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4304
              have b26e4362 : x = (M.op y y) := by
                first
                | (have i₁ := b26e4332
                   have i₂ := b26e16 x
                   grind)
                | exact superpose b26e16 b26e4332
                | exact resolve b26e4332 b26e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b26e4332
              have b26e4376 : False := by grind
              exact b26e4376

/-- `Equation2146`: `x = ((y ◇ y) ◇ z) ◇ (x ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_y_pxy_Equation2146 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2146 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2146.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
        intro X0
        grind
      have b0e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        grind
      clear b0e28
      have b0e76 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e81 : False := by grind
      exact b0e81
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) X2) (M.op X0 X2)) = X0 := by
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
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
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
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e33 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op X1 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X0 (M.op X1 X1)))) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op X1 X1) (M.op X0 (M.op X1 X1))
               have i₂ := b4e13 X0 X1 (M.op X1 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) x) := by
            intro X0
            first
            | (have i₁ := b4e13 y X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e13 (M.op (M.op X3 X3) X2) X1 (M.op X0 X2)
               have i₂ := b4e13 X0 X3 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op (M.op x (M.op X0 X1)) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e33 (M.op X0 X1) (M.op (M.op X2 X2) X1)
               have i₂ := b4e13 X0 X2 X1
               grind)
            | exact superpose b4e13 b4e33
            | exact resolve b4e33 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (M.op X0 X1) (M.op x X1)
               have i₂ := b4e33 X1 X0
               grind)
            | exact superpose b4e33 b4e33
            | exact resolve b4e33 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) X0) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 (M.op x X2) X1 (M.op X0 X2)
               have i₂ := b4e33 X2 X0
               grind)
            | exact superpose b4e33 b4e13
            | exact resolve b4e13 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X1 X2 : G, (M.op (M.op X2 X2) X1) = (M.op x X1) := by
            intro X1 X2
            first
            | (have i₁ := b4e42 x X1 X2
               have i₂ := b4e43 x X1
               grind)
            | exact superpose b4e43 b4e42
            | exact resolve b4e42 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e73 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e63 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e63
            | (have j0 := b4e63 X0 X1
               grind)
            | exact resolve b4e63 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e63
          have b4e88 : y = (M.op (M.op (σ x) y) x) := by
            first
            | (have i₁ := b4e37 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e37
            | exact resolve b4e37 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e95 : (M.op (M.op x x) y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e33 x (M.op (σ x) y)
               have i₂ := b4e88
               grind)
            | exact superpose b4e88 b4e33
            | exact resolve b4e33 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e98 : (M.op x y) = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e95
               have i₂ := b4e47 y x
               grind)
            | exact superpose b4e47 b4e95
            | exact resolve b4e95 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e110 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op X0 X0) y) (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) X0 y
               have i₂ := b4e98
               grind)
            | exact superpose b4e98 b4e13
            | exact resolve b4e13 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : x = (σ x) := by
            first
            | (have i₁ := b4e110 x
               have i₂ := b4e13 x x y
               grind)
            | exact superpose b4e13 b4e110
            | exact resolve b4e110 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110
          have b4e129 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e20
            | exact resolve b4e20 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e131 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 x
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e19
            | exact resolve b4e19 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : x = (τ x) := by
            first
            | (have i₁ := b4e14 x
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e14
            | exact resolve b4e14 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e215 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b4e36 (M.op X0 X0) X0 X1
               grind)
            | exact superpose b4e36 b4e36
            | exact resolve b4e36 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e218 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e36 X0 X1 (M.op x (M.op X1 X1))
               have i₂ := b4e33 (M.op X1 X1) X0
               grind)
            | exact superpose b4e33 b4e36
            | exact resolve b4e36 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e291 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 x)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e33 x X1
               have i₂ := b4e215 X0 x
               grind)
            | (have i₁ := b4e33 x X1
               have i₂ := b4e215 x X0
               grind)
            | exact superpose b4e215 b4e33
            | exact resolve b4e33 b4e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e292 : ∀ X0 : G, (M.op X0 X0) = x := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e215 X0 y
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e215 y X0
               grind)
            | exact superpose b4e215 b4e22
            | exact resolve b4e22 b4e215
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e215
          have b4e293 : ∀ X1 : G, (M.op x (M.op X1 x)) = X1 := by
            intro X1
            first
            | (have i₁ := b4e291 x X1
               have i₂ := b4e47 (M.op X1 x) x
               grind)
            | exact superpose b4e47 b4e291
            | exact resolve b4e291 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e291
          have b4e430 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op (M.op X4 X4) X0) X2) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b4e39 X2 X4 (M.op X0 (M.op X2 (M.op X3 X3))) X1
               have i₂ := b4e36 X2 X3 X0
               grind)
            | exact superpose b4e36 b4e39
            | exact resolve b4e39 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e529 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X2 (M.op X3 X3)))) = (M.op (M.op x X0) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e430 X0 X1 X2 X3 x
               have i₂ := b4e47 X0 x
               grind)
            | exact superpose b4e47 b4e430
            | exact resolve b4e430 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e430
          have b4e586 : ∀ X0 X2 X3 : G, (M.op (M.op x X0) X2) = (M.op x (M.op X0 (M.op X2 (M.op X3 X3)))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e529 X0 x X2 X3
               have i₂ := b4e47 (M.op X0 (M.op X2 (M.op X3 X3))) x
               grind)
            | exact superpose b4e47 b4e529
            | exact resolve b4e529 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e529
          have b4e616 : ∀ X0 X2 : G, (M.op (M.op x X0) X2) = (M.op x (M.op X0 (M.op X2 x))) := by
            intro X0 X2
            first
            | (have i₁ := b4e586 X0 X2 x
               have i₂ := b4e292 x
               grind)
            | exact superpose b4e292 b4e586
            | exact resolve b4e586 b4e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e586
          have b4e655 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) X1) ∨ (k X3 (M.op X2 X2)) = (M.op X3 (M.op X2 X2)) ∨ (M.op X2 X2) = X3 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e73 X3 (M.op X2 X2)
               have i₂ := b4e39 X1 X0 (M.op X2 X2) X2
               grind)
            | exact superpose b4e39 b4e73
            | (have j0 := b4e73 X3 (M.op X2 X2)
               grind)
            | exact resolve b4e73 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e73
          have b4e660 : ∀ X2 X3 : G, (M.op X2 X2) ≠ (M.op x (M.op X2 X2)) ∨ (k X3 (M.op X2 X2)) = (M.op X3 (M.op X2 X2)) ∨ (M.op X2 X2) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b4e655 x x X2 X3
               have i₂ := b4e46 x x (M.op X2 X2)
               grind)
            | exact superpose b4e46 b4e655
            | (have j0 := b4e655 x x X2 X3
               grind)
            | exact resolve b4e655 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e655
          have b4e666 : ∀ X2 X3 : G, (k X3 (M.op X2 X2)) = (M.op X3 (M.op X2 X2)) ∨ (M.op X2 X2) = X3 := by
            intro X2 X3
            first
            | (have j0 := b4e660 X2 X3
               grind)
            | (have r₁ := b4e660 x X3
               have r₂ := b4e218 x x
               grind)
            | exact resolve b4e660 b4e218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e218 b4e660
          have b4e669 : ∀ X2 X3 : G, (k X3 x) = (M.op X3 x) ∨ (M.op X2 X2) = X3 := by
            intro X2 X3
            first
            | (have i₁ := b4e666 x X3
               have i₂ := b4e292 x
               grind)
            | exact superpose b4e292 b4e666
            | (have j0 := b4e666 X2 X3
               grind)
            | exact resolve b4e666 b4e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e666
          have b4e672 : ∀ X3 : G, (k X3 x) = (M.op X3 x) ∨ x = X3 := by
            intro X3
            first
            | (have i₁ := b4e669 x X3
               have i₂ := b4e292 x
               grind)
            | exact superpose b4e292 b4e669
            | (have j0 := b4e669 x X3
               grind)
            | exact resolve b4e669 b4e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e669
          have b4e1231 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op x (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (σ X1) (σ X0)
               have i₂ := b4e77 X0 X1
               grind)
            | exact superpose b4e77 b4e33
            | (have j1 := b4e77 X0 X1
               grind)
            | exact resolve b4e33 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e77
          have b4e1260 : ∀ X0 X1 : G, (σ X0) = (σ x) ∨ (σ X0) = (M.op (M.op x (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e1231 X0 X1
               have i₂ := b4e292 X1
               grind)
            | exact superpose b4e292 b4e1231
            | (have j0 := b4e1231 X0 X1
               grind)
            | exact resolve b4e1231 b4e292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292 b4e1231
          have b4e1311 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op x (σ X1)) (σ (k X0 X1))) ∨ (σ X0) = x ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e1260 X0 X1
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e1260
            | (have j0 := b4e1260 X0 X1
               grind)
            | exact resolve b4e1260 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1260
          have b4e2320 : ∀ X0 : G, (k X0 (σ x)) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b4e27 X0 x
               have i₂ := b4e672 (τ X0)
               grind)
            | exact superpose b4e672 b4e27
            | (have j1 := b4e672 (τ X0)
               grind)
            | exact resolve b4e27 b4e672
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e672
          have b4e2323 : ∀ X0 : G, (k X0 x) = (σ (M.op (τ X0) x)) ∨ (τ X0) = x := by
            intro X0
            first
            | (have i₁ := b4e2320 X0
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e2320
            | (have j0 := b4e2320 X0
               grind)
            | exact resolve b4e2320 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2320
          have b4e4235 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op (M.op x X0) X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e43 X0 (M.op X1 x)
               have i₂ := b4e616 X0 X1
               grind)
            | exact superpose b4e616 b4e43
            | exact resolve b4e43 b4e616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43 b4e616
          have b4e4272 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e4235 X0 X1
               have i₂ := b4e293 X1
               grind)
            | (have i₁ := b4e4235 X0 X1
               have i₂ := b4e293 (M.op x (M.op X1 x))
               grind)
            | exact superpose b4e293 b4e4235
            | exact resolve b4e4235 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4235
          have b4e4331 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 x)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e4272 (M.op X0 x) X1
               have i₂ := b4e293 X0
               grind)
            | exact superpose b4e293 b4e4272
            | exact resolve b4e4272 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4272
          have b4e7035 : ∀ X0 : G, (k (σ X0) x) = (σ (M.op X0 x)) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e2323 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e2323
            | exact resolve b4e2323 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2323
          have b4e7069 : ∀ X0 : G, (σ (k X0 x)) = (σ (M.op X0 x)) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e7035 X0
               have i₂ := b4e131 X0
               grind)
            | exact superpose b4e131 b4e7035
            | (have j0 := b4e7035 X0
               grind)
            | exact resolve b4e7035 b4e131
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e131 b4e7035
          have b4e11910 : ∀ X0 : G, (σ X0) = (M.op (M.op x (σ x)) (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e1311 X0 x
               have i₂ := b4e7069 X0
               grind)
            | exact superpose b4e7069 b4e1311
            | (have j0 := b4e1311 X0 x
               have j1 := b4e7069 (σ X0)
               grind)
            | exact resolve b4e1311 b4e7069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1311 b4e7069
          have b4e11965 : ∀ X0 : G, (σ X0) = (M.op (M.op x x) (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e11910 X0
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e11910
            | (have j0 := b4e11910 X0
               grind)
            | exact resolve b4e11910 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e11910
          have b4e12004 : ∀ X0 : G, (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ (σ X0) = (σ x) ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e11965 X0
               have i₂ := b4e47 (σ (M.op X0 x)) x
               grind)
            | exact superpose b4e47 b4e11965
            | (have j0 := b4e11965 X0
               grind)
            | exact resolve b4e11965 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e11965
          have b4e12028 : ∀ X0 : G, (σ X0) = x ∨ (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ x = X0 := by
            intro X0
            first
            | (have i₁ := b4e12004 X0
               have i₂ := b4e111
               grind)
            | exact superpose b4e111 b4e12004
            | (have j0 := b4e12004 X0
               grind)
            | exact resolve b4e12004 b4e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111 b4e12004
          have b4e12029 : ∀ X0 : G, (σ X0) = (M.op x (σ (M.op X0 x))) ∨ (σ X0) = x ∨ x = X0 := by
            intro X0
            first
            | (have j0 := b4e12028 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12028
          have b4e128472 : (M.op x (σ y)) = (σ (M.op (σ x) y)) ∨ x = (σ (M.op (σ x) y)) ∨ x = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e12029 (M.op (σ x) y)
               have i₂ := b4e88
               grind)
            | exact superpose b4e88 b4e12029
            | (have j0 := b4e12029 (M.op (σ x) y)
               grind)
            | exact resolve b4e12029 b4e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e88 b4e12029
          have b4e128569 : (σ (M.op x y)) = (M.op x (σ y)) ∨ x = (σ (M.op (σ x) y)) ∨ x = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e128472
               have i₂ := b4e98
               grind)
            | exact superpose b4e98 b4e128472
            | exact resolve b4e128472 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128472
          have b4e128585 : x = (σ (M.op (σ x) y)) ∨ x = (M.op (σ x) y) := by
            first
            | (have r₁ := b4e128569
               have r₂ := b4e129
               grind)
            | exact resolve b4e128569 b4e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e129 b4e128569
          have b4e128591 : x = (σ (M.op x y)) ∨ x = (M.op (σ x) y) := by
            first
            | (have i₁ := b4e128585
               have i₂ := b4e98
               grind)
            | exact superpose b4e98 b4e128585
            | exact resolve b4e128585 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128585
          have b4e128593 : x = (σ (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e128591
               have i₂ := b4e98
               grind)
            | exact superpose b4e98 b4e128591
            | exact resolve b4e128591 b4e98
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98 b4e128591
          have b4e128993 : (M.op x y) = (τ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e128593
               grind)
            | exact superpose b4e128593 b4e14
            | exact resolve b4e14 b4e128593
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e128593
          have b4e129102 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e128993
               have i₂ := b4e133
               grind)
            | exact superpose b4e133 b4e128993
            | exact resolve b4e128993 b4e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133 b4e128993
          have b4e129103 : x = (M.op x y) := by grind
          clear b4e129102
          have b4e129590 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e4331 x y
               have i₂ := b4e129103
               grind)
            | exact superpose b4e129103 b4e4331
            | exact resolve b4e4331 b4e129103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4331 b4e129103
          have b4e129608 : x = y := by
            first
            | (have i₁ := b4e129590
               have i₂ := b4e293 x
               grind)
            | (have i₁ := b4e129590
               have i₂ := b4e293 (M.op x (M.op x x))
               grind)
            | exact superpose b4e293 b4e129590
            | exact resolve b4e129590 b4e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293 b4e129590
          have b4e129634 : False := by grind
          exact b4e129634
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e176 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e191 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e176
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e176
            | exact resolve b5e176 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e176
          have b5e192 : False := by grind
          exact b5e192
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
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
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e102 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e135 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e102
               grind)
            | exact superpose b7e102 b7e14
            | exact resolve b7e14 b7e102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e136 : x = (M.op y y) := by
            first
            | (have i₁ := b7e135
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e135
            | exact resolve b7e135 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135
          have b7e140 : False := by grind
          exact b7e140
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : x ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e62 X0 X1
               have i₂ := b8e31 X1
               grind)
            | exact superpose b8e31 b8e62
            | (have j0 := b8e62 X0 X1
               grind)
            | exact resolve b8e62 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e78 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e31 y
               grind)
            | exact superpose b8e31 b8e24
            | exact resolve b8e24 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e382 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e72 x y
               grind)
            | exact superpose b8e72 b8e20
            | (have j1 := b8e72 x y
               grind)
            | exact resolve b8e20 b8e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e72
          have b8e416 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e382
               have r₂ := b8e78
               grind)
            | exact resolve b8e382 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78 b8e382
          have b8e426 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e416
               have r₂ := b8e23
               grind)
            | exact resolve b8e416 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e416
          have b8e785 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e426
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e426
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e426
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e426
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e426 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e426
          have b8e787 : x = (M.op y y) ∨ x = y := by grind
          clear b8e785
          have b8e791 : x = y := by
            first
            | (have r₁ := b8e787
               have r₂ := b8e22
               grind)
            | exact resolve b8e787 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e787
          have b8e795 : False := by grind
          exact b8e795
