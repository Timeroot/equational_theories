import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4434`: `x ◇ (y ◇ x) = (x ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation4434 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4434 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4434.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e73 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e78 : False := by grind
      exact b0e78
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
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
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e34 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b4e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1 x
               have i₂ := b4e13 X0 X2 x
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e35 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e44 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e34 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op X0 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 (σ y) X1
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e105 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e26
          have b4e112 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e105 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e105
            | exact resolve b4e105 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e113 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e112
          have b4e304 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e41 X0 X1 y
               have i₂ := b4e43 X0
               grind)
            | exact superpose b4e43 b4e41
            | exact resolve b4e41 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e43
          have b4e379 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e304 X0 (σ y)
               have i₂ := b4e44 X0
               grind)
            | exact superpose b4e44 b4e304
            | exact resolve b4e304 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e304
          have b4e517 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e379 (σ x)
               grind)
            | exact superpose b4e379 b4e20
            | exact resolve b4e20 b4e379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2094 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op (τ X0) (τ X0))
               have i₂ := b4e113 X0
               grind)
            | exact superpose b4e113 b4e30
            | exact resolve b4e30 b4e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e113
          have b4e2100 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e2094 X0
               have i₂ := b4e58 (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e58 b4e2094
            | exact resolve b4e2094 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2094
          have b4e2103 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2100 X0
               have i₂ := b4e379 (τ X0)
               grind)
            | exact superpose b4e379 b4e2100
            | exact resolve b4e2100 b4e379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2100
          have b4e2104 : ∀ X0 : G, (M.op X0 (σ y)) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2103 X0
               have i₂ := b4e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e58 b4e2103
            | exact resolve b4e2103 b4e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e58 b4e2103
          have b4e2105 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2104 X0
               have i₂ := b4e379 X0
               grind)
            | exact superpose b4e379 b4e2104
            | exact resolve b4e2104 b4e379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e379 b4e2104
          have b4e2644 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e2105 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e2105
            | exact resolve b4e2105 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2105
          have b4e2914 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e517
               have i₂ := b4e2644 x
               grind)
            | exact superpose b4e2644 b4e517
            | (have r₁ := b4e517
               have r₂ := b4e2644 x
               grind)
            | exact resolve b4e517 b4e2644
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517 b4e2644
          have b4e2928 : False := by grind
          exact b4e2928
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e117 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e122 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e117
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e117
            | exact resolve b5e117 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e117
          have b5e123 : False := by grind
          exact b5e123
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X0) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
          have b7e41 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e32 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e90 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e41 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e41
            | exact resolve b7e41 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e41
          have b7e98 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e90
               grind)
            | exact superpose b7e90 b7e14
            | exact resolve b7e14 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90
          have b7e99 : y = (M.op y y) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e98
            | exact resolve b7e98 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e103 : False := by grind
          exact b7e103
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e61 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e61
            | (have j0 := b8e61 X0 X1
               grind)
            | exact resolve b8e61 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e76 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e1859 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e70 x y
               grind)
            | exact superpose b8e70 b8e20
            | (have j1 := b8e70 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70
          have b8e1898 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1859
               have r₂ := b8e76
               grind)
            | exact resolve b8e1859 b8e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76 b8e1859
          have b8e1911 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1898
               have r₂ := b8e23
               grind)
            | exact resolve b8e1898 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1898
          have b8e1930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e1911
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1911
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e1911
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1911
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1911 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1911
          have b8e1931 : y = (M.op y y) ∨ x = y := by grind
          clear b8e1930
          have b8e1934 : x = y := by
            first
            | (have r₁ := b8e1931
               have r₂ := b8e22
               grind)
            | exact resolve b8e1931 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1931
          have b8e1938 : False := by grind
          exact b8e1938

/-- `Equation4437`: `x ◇ (y ◇ x) = (x ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4437 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4437 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4437.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
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
      have b0e41 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
      have b0e42 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e44 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
        intro X0 X1
        grind
      have b0e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e92 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e95 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X1
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e98 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e18
        | exact resolve b0e18 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e171 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) := by
        intro X0
        grind
      clear b0e95
      have b0e318 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e44 y X0
           have i₂ := b0e42 (M.op X0 y)
           grind)
        | exact superpose b0e42 b0e44
        | exact resolve b0e44 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e321 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
        first
        | (have i₁ := b0e318 x
           have i₂ := b0e42 x
           grind)
        | exact superpose b0e42 b0e318
        | exact resolve b0e318 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e318
      have b0e890 : ∀ X0 : G, (k y (τ (M.op (σ y) X0))) = (τ (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e92 y (M.op (σ y) X0)
           have i₂ := b0e171 X0
           grind)
        | exact superpose b0e171 b0e92
        | exact resolve b0e92 b0e171
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e92 b0e171
      have b0e892 : ∀ X0 : G, y = (k y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e890 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e890
        | exact resolve b0e890 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e890
      have b0e920 : ∀ X0 : G, y = (M.op y (τ (M.op (σ y) X0))) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e16 y (τ (M.op (σ y) X0))
           have i₂ := b0e892 X0
           grind)
        | exact superpose b0e892 b0e16
        | (have j0 := b0e16 y (τ (M.op (σ y) X0))
           grind)
        | exact resolve b0e16 b0e892
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e892
      have b0e921 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e920 X0
           have i₂ := b0e42 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e42 b0e920
        | (have j0 := b0e920 X0
           grind)
        | exact resolve b0e920 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e920
      have b0e926 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (τ (M.op (σ y) X0)) = (M.op y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e921 X0
           have i₂ := b0e42 y
           grind)
        | exact superpose b0e42 b0e921
        | (have j0 := b0e921 X0
           grind)
        | exact resolve b0e921 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e921
      have b0e928 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e926 X0
           have i₂ := b0e42 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e42 b0e926
        | (have j0 := b0e926 X0
           grind)
        | exact resolve b0e926 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e926
      have b0e929 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have j0 := b0e928 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e928
      have b0e1756 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e66 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e1758 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e1756 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1756
      have b0e13656 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op (σ y) X0)
           have i₂ := b0e929 X0
           grind)
        | exact superpose b0e929 b0e13
        | exact resolve b0e13 b0e929
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e929
      have b0e13664 : y = (M.op x y) := by
        first
        | (have r₁ := b0e13656 x
           have r₂ := b0e98 x
           grind)
        | exact resolve b0e13656 b0e98
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13656
      have b0e14797 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e98 X0
           have i₂ := b0e13664
           grind)
        | exact superpose b0e13664 b0e98
        | exact resolve b0e98 b0e13664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98
      have b0e14799 : y = (k y y) := by
        first
        | (have i₁ := b0e321
           have i₂ := b0e13664
           grind)
        | exact superpose b0e13664 b0e321
        | exact resolve b0e321 b0e13664
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e321 b0e13664
      have b0e16450 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e1758 y
           have i₂ := b0e14799
           grind)
        | exact superpose b0e14799 b0e1758
        | (have j0 := b0e1758 y
           grind)
        | exact resolve b0e1758 b0e14799
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1758 b0e14799
      have b0e16456 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e16450
      have b0e16462 : False := by grind
      exact b0e16462
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
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
        have b1e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b1e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b1e95 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e13 (k X0 (τ X1))
             have i₂ := b1e27 X1 X0
             grind)
          | exact superpose b1e27 b1e13
          | exact resolve b1e13 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e338 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b1e95
        have b1e351 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e338 X0
             have i₂ := b1e13 X0
             grind)
          | exact superpose b1e13 b1e338
          | exact resolve b1e338 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e338
        have b1e1983 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e63 x x
             grind)
          | exact superpose b1e63 b1e21
          | (have j1 := b1e63 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e63 x y
             grind)
          | exact resolve b1e21 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63
        have b1e2058 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e1983
        have b1e15664 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e2058
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e2058
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e2058 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e2058
        have b1e15665 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e15664
        have b1e15667 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e15665
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15665
          | exact resolve b1e15665 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15665
        have b1e15668 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e15667
        have b1e15676 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e15668
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15668
          | exact resolve b1e15668 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15668
        have b1e15691 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b1e351 x
             have i₂ := b1e15676
             grind)
          | exact superpose b1e15676 b1e351
          | exact resolve b1e351 b1e15676
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e351 b1e15676
        have b1e15741 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b1e15691
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e15691
          | exact resolve b1e15691 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15691
        have b1e15807 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b1e17 x x
             have i₂ := b1e15741
             grind)
          | exact superpose b1e15741 b1e17
          | (have j0 := b1e17 x x
             grind)
          | exact resolve b1e17 b1e15741
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15741
        have b1e15808 : x = (M.op x x) ∨ x = y := by grind
        clear b1e15807
        have b1e15821 : x = y ∨ x = y := by
          first
          | (have i₁ := b1e15808
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15808
          | exact resolve b1e15808 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15808
        have b1e15822 : x = y := by grind
        clear b1e15821
        have b1e16269 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e15822
             grind)
          | exact superpose b1e15822 b1e24
          | exact resolve b1e24 b1e15822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e16316 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e16269
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e16269
          | exact resolve b1e16269 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e16269
        have b1e16326 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e16316
             have i₂ := b1e15822
             grind)
          | exact superpose b1e15822 b1e16316
          | exact resolve b1e16316 b1e15822
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e15822 b1e16316
        have b1e16327 : False := by grind
        exact b1e16327
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
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
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X3
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e88 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e268 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e88
        have b2e281 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e268 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e268
          | exact resolve b2e268 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e268
        have b2e1078 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e64 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e1079 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1078
             have r₂ := b2e22
             grind)
          | exact resolve b2e1078 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1078
        have b2e1080 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1079
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1079
          | exact resolve b2e1079 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1079
        have b2e1081 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1080
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1080
          | exact resolve b2e1080 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1080
        have b2e1085 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1081
             grind)
          | exact superpose b2e1081 b2e22
          | exact resolve b2e22 b2e1081
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1091 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e30 (σ x) (σ y) x x
             have i₂ := b2e1081
             grind)
          | exact superpose b2e1081 b2e30
          | exact resolve b2e30 b2e1081
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e1585 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e1081
             have i₂ := b2e1091 (σ y) X0
             grind)
          | (have i₁ := b2e1081
             have i₂ := b2e1091 X0 (σ y)
             grind)
          | exact superpose b2e1091 b2e1081
          | exact resolve b2e1081 b2e1091
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1081 b2e1091
        have b2e1721 : x = (k x (τ (σ x))) := by
          first
          | (have i₁ := b2e281 x
             have i₂ := b2e1585 (σ x)
             grind)
          | exact superpose b2e1585 b2e281
          | exact resolve b2e281 b2e1585
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e281 b2e1585
        have b2e1765 : x = (k x x) := by
          first
          | (have i₁ := b2e1721
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e1721
          | exact resolve b2e1721 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1721
        have b2e1806 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e1765
             grind)
          | exact superpose b2e1765 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e1765
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1765
        have b2e1807 : x = (M.op x x) := by grind
        clear b2e1806
        have b2e1871 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e1807
             grind)
          | exact superpose b2e1807 b2e20
          | exact resolve b2e20 b2e1807
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1807
        have b2e2109 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1085
             have i₂ := b2e1871
             grind)
          | exact superpose b2e1871 b2e1085
          | exact resolve b2e1085 b2e1871
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1085 b2e1871
        have b2e2111 : False := by grind
        exact b2e2111
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b3e48 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
        have b3e102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e157 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e24
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e24
          | exact resolve b3e24 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24
        have b3e164 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (σ y) X0 X1
             have i₂ := b3e48 X0
             grind)
          | exact superpose b3e48 b3e12
          | exact resolve b3e12 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e167 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) := by
          intro X1
          first
          | (have i₁ := b3e164 x X1
             have i₂ := b3e48 (M.op x (σ y))
             grind)
          | exact superpose b3e48 b3e164
          | exact resolve b3e164 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e164
        have b3e1744 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e102 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e102
          | exact resolve b3e102 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e1850 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e1744
        have b3e2190 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e1850
             grind)
          | exact superpose b3e1850 b3e13
          | exact resolve b3e13 b3e1850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2207 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2190
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2190
          | exact resolve b3e2190 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2190
        have b3e2553 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e2207
             grind)
          | exact superpose b3e2207 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e2207
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2207
        have b3e2554 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2553
        have b3e2556 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e2554
             have r₂ := b3e20
             grind)
          | exact resolve b3e2554 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2554
        have b3e2661 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e2556
        have b3e2971 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e1850
             have i₂ := b3e2661
             grind)
          | exact superpose b3e2661 b3e1850
          | exact resolve b3e1850 b3e2661
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1850 b3e2661
        have b3e2980 : (σ x) = (σ y) := by grind
        clear b3e2971
        have b3e3025 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) X0) := by
          intro X0
          first
          | (have i₁ := b3e167 x
             have i₂ := b3e2980
             grind)
          | exact superpose b3e2980 b3e167
          | exact resolve b3e167 b3e2980
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e167 b3e2980
        have b3e3051 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e3025 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e3025
          | exact resolve b3e3025 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3025
        have b3e3057 : False := by grind
        exact b3e3057
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
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
          have b5e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          have b5e65 : y = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e62
          have b5e67 : x = (k x y) := by
            first
            | (have r₁ := b5e65
               have r₂ := b5e21
               grind)
            | exact resolve b5e65 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b5e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b5e854 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
            intro X0
            grind
          clear b5e108
          have b5e867 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e854 X0
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e854
            | exact resolve b5e854 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e854
          have b5e1099 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b5e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e1100 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1099
               have r₂ := b5e24
               grind)
            | exact resolve b5e1099 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1099
          have b5e1101 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1100
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1100
            | exact resolve b5e1100 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1100
          have b5e1102 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1101
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e1101
            | exact resolve b5e1101 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e1101
          have b5e1111 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 (σ x) (σ y) x x
               have i₂ := b5e1102
               grind)
            | exact superpose b5e1102 b5e37
            | exact resolve b5e37 b5e1102
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1454 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e1102
               have i₂ := b5e1111 (σ y) X0
               grind)
            | (have i₁ := b5e1102
               have i₂ := b5e1111 X0 (σ y)
               grind)
            | exact superpose b5e1111 b5e1102
            | exact resolve b5e1102 b5e1111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1102 b5e1111
          have b5e1675 : x = (k x (τ (σ x))) := by
            first
            | (have i₁ := b5e867 x
               have i₂ := b5e1454 (σ x)
               grind)
            | exact superpose b5e1454 b5e867
            | exact resolve b5e867 b5e1454
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e867 b5e1454
          have b5e1718 : x = (k x x) := by
            first
            | (have i₁ := b5e1675
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e1675
            | exact resolve b5e1675 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1675
          have b5e1793 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e1718
               grind)
            | exact superpose b5e1718 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e1718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1718
          have b5e1794 : x = (M.op x x) := by grind
          clear b5e1793
          have b5e2023 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e37 x x x x
               have i₂ := b5e1794
               grind)
            | exact superpose b5e1794 b5e37
            | exact resolve b5e37 b5e1794
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e1794
          have b5e2499 : ∀ X0 : G, y ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e21
               have i₂ := b5e2023 x X0
               grind)
            | (have i₁ := b5e21
               have i₂ := b5e2023 X0 x
               grind)
            | exact superpose b5e2023 b5e21
            | exact resolve b5e21 b5e2023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2500 : ∀ X0 : G, y = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e2023 y X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e2023 X0 y
               grind)
            | exact superpose b5e2023 b5e22
            | exact resolve b5e22 b5e2023
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2023
          have b5e2543 : False := by grind
          exact b5e2543
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
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
        have b6e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X0 X1 X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e87 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e89 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e99 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e89
             have r₂ := b6e20
             grind)
          | exact resolve b6e89 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e89
        have b6e102 : x = (M.op x y) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e21
             grind)
          | exact resolve b6e99 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e104 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e102
             grind)
          | exact superpose b6e102 b6e21
          | exact resolve b6e21 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e120 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 x y x x
             have i₂ := b6e102
             grind)
          | exact superpose b6e102 b6e43
          | exact resolve b6e43 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e281 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e102
             have i₂ := b6e120 y X0
             grind)
          | (have i₁ := b6e102
             have i₂ := b6e120 X0 y
             grind)
          | exact superpose b6e120 b6e102
          | exact resolve b6e102 b6e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e120
        have b6e375 : x = (k x x) := by grind
        clear b6e281
        have b6e1419 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e87 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e87
          | exact resolve b6e87 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e1517 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1419
        have b6e1549 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1517
             have i₂ := b6e375
             grind)
          | exact superpose b6e375 b6e1517
          | exact resolve b6e1517 b6e375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e375 b6e1517
        have b6e1550 : (σ x) = (σ y) := by grind
        clear b6e1549
        have b6e1613 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e1550
             grind)
          | exact superpose b6e1550 b6e13
          | exact resolve b6e13 b6e1550
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1550
        have b6e1623 : x = y := by
          first
          | (have i₁ := b6e1613
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e1613
          | exact resolve b6e1613 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1613
        have b6e1629 : False := by grind
        exact b6e1629
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X1) X2) := by
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
          have b7e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            grind
          have b7e47 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e50 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e47
          have b7e52 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e50
               have r₂ := b7e23
               grind)
            | exact resolve b7e50 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e53 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e52
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e52
            | exact resolve b7e52 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e52
          have b7e56 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e14
            | exact resolve b7e14 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e57 : x = (k x y) := by
            first
            | (have i₁ := b7e56
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e56
            | exact resolve b7e56 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e69 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X1 X0) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X1 X0
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e75 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e57
               grind)
            | exact superpose b7e57 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e57
          have b7e76 : x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b7e75
               have r₂ := b7e21
               grind)
            | exact resolve b7e75 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : x = (M.op x y) := by
            first
            | (have r₁ := b7e76
               have r₂ := b7e22
               grind)
            | exact resolve b7e76 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76
          have b7e104 : ∀ X0 X1 : G, (M.op x X0) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 x y x x
               have i₂ := b7e78
               grind)
            | exact superpose b7e78 b7e32
            | exact resolve b7e32 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e283 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e78
               have i₂ := b7e104 y X0
               grind)
            | (have i₁ := b7e78
               have i₂ := b7e104 X0 y
               grind)
            | exact superpose b7e104 b7e78
            | exact resolve b7e78 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78
          have b7e335 : ∀ X0 X1 : G, (M.op x X1) = (k (M.op x X1) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e38 x X1
               have i₂ := b7e104 (M.op X1 x) X0
               grind)
            | (have i₁ := b7e38 x X1
               have i₂ := b7e104 X0 (M.op X1 x)
               grind)
            | exact superpose b7e104 b7e38
            | exact resolve b7e38 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e104
          have b7e338 : ∀ X1 : G, (M.op x X1) = (k (M.op x X1) x) := by
            intro X1
            first
            | (have i₁ := b7e335 x X1
               have i₂ := b7e283 x
               grind)
            | exact superpose b7e283 b7e335
            | exact resolve b7e335 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e335
          have b7e350 : x = (k x x) := by
            first
            | (have i₁ := b7e338 x
               have i₂ := b7e283 x
               grind)
            | exact superpose b7e283 b7e338
            | exact resolve b7e338 b7e283
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e283 b7e338
          have b7e1005 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e69 (σ x) (σ x) X0
               grind)
            | (have i₁ := b7e23
               have i₂ := b7e69 (σ x) x (σ x)
               grind)
            | exact superpose b7e69 b7e23
            | (have j1 := b7e69 (σ x) (σ x) x
               grind)
            | exact resolve b7e23 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e1083 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ y) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e1005 X0
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e1005
            | (have j0 := b7e1005 X0
               grind)
            | exact resolve b7e1005 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1005
          have b7e1104 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have i₁ := b7e1083 X0
               have i₂ := b7e350
               grind)
            | exact superpose b7e350 b7e1083
            | (have j0 := b7e1083 X0
               grind)
            | exact resolve b7e1083 b7e350
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e350 b7e1083
          have b7e1105 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have j0 := b7e1104 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1104
          have b7e11660 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e1105 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e1105
            | (have r₁ := b7e1105 (σ y)
               have r₂ := b7e24
               grind)
            | exact resolve b7e1105 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1105
          have b7e11684 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b7e11660
          have b7e11706 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 (σ x) (σ x) x x
               have i₂ := b7e11684
               grind)
            | exact superpose b7e11684 b7e32
            | exact resolve b7e32 b7e11684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32 b7e11684
          have b7e11934 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e11706 (σ x) X0
               grind)
            | (have i₁ := b7e23
               have i₂ := b7e11706 X0 (σ x)
               grind)
            | exact superpose b7e11706 b7e23
            | exact resolve b7e23 b7e11706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e11935 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e11706 (σ y) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e11706 X0 (σ y)
               grind)
            | exact superpose b7e11706 b7e24
            | exact resolve b7e24 b7e11706
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e11706
          have b7e12036 : False := by grind
          exact b7e12036
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
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e1146 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1147 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1146
               have r₂ := b8e24
               grind)
            | exact resolve b8e1146 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1146
          have b8e1148 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1147
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1147
            | exact resolve b8e1147 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1147
          have b8e1151 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1148
               grind)
            | exact superpose b8e1148 b8e20
            | exact resolve b8e20 b8e1148
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1148
          have b8e1554 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1151
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1151
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1151 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1151
          have b8e1555 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1554
          have b8e1558 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1555
               have r₂ := b8e21
               grind)
            | exact resolve b8e1555 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1555
          have b8e1561 : False := by grind
          exact b8e1561

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation4441 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4441 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
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
      have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e79 : False := by grind
      exact b0e79
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
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
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
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e34 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 y X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e46 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e40 x X2
               have i₂ := b4e40 x X0
               grind)
            | (have i₁ := b4e40 X0 x
               have i₂ := b4e40 X0 (M.op X0 y)
               grind)
            | exact superpose b4e40 b4e40
            | exact resolve b4e40 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e83 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e22
               have i₂ := b4e46 y X0
               grind)
            | (have i₁ := b4e22
               have i₂ := b4e46 X0 y
               grind)
            | exact superpose b4e46 b4e22
            | exact resolve b4e22 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e112 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op X0 y) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 y X1 X2
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e13
            | exact resolve b4e13 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83
          have b4e132 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op X0 (σ y)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 X0 (M.op (σ y) x) X2 X3
               have i₂ := b4e43 x X0
               grind)
            | exact superpose b4e43 b4e13
            | exact resolve b4e13 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e136 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e132 X0 x x
               have i₂ := b4e112 X0 x x
               grind)
            | exact superpose b4e112 b4e132
            | exact resolve b4e132 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132
          have b4e141 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e26
          have b4e148 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e141 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e141
            | exact resolve b4e141 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141
          have b4e149 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b4e148
          have b4e186 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e136 (σ x)
               grind)
            | exact superpose b4e136 b4e20
            | exact resolve b4e20 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e2339 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e30 (M.op (τ X0) (τ X0))
               have i₂ := b4e149 X0
               grind)
            | exact superpose b4e149 b4e30
            | exact resolve b4e30 b4e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e149
          have b4e2345 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b4e2339 X0
               have i₂ := b4e112 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e112 b4e2339
            | exact resolve b4e2339 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2339
          have b4e2348 : ∀ X0 : G, (M.op X0 y) = (σ (M.op (τ X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e2345 X0
               have i₂ := b4e112 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b4e112 b4e2345
            | exact resolve b4e2345 b4e112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112 b4e2345
          have b4e2380 : ∀ X0 : G, (M.op (σ X0) y) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e2348 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e2348
            | exact resolve b4e2348 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2348
          have b4e2689 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e186
               have i₂ := b4e2380 x
               grind)
            | exact superpose b4e2380 b4e186
            | (have r₁ := b4e186
               have r₂ := b4e2380 x
               grind)
            | exact resolve b4e186 b4e2380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e186 b4e2380
          have b4e2711 : False := by grind
          exact b4e2711
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e257 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30
          have b5e266 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e257
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e257
            | exact resolve b5e257 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e257
          have b5e267 : False := by grind
          exact b5e267
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
        · have b7e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
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
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ y) (σ y) X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e32 X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e43 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b7e42 (σ y) X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e42
            | exact resolve b7e42 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e110 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e43 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e43
            | exact resolve b7e43 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e43
          have b7e128 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e110
               grind)
            | exact superpose b7e110 b7e14
            | exact resolve b7e14 b7e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e129 : y = (M.op y y) := by
            first
            | (have i₁ := b7e128
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e128
            | exact resolve b7e128 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e133 : False := by grind
          exact b7e133
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X0 X1
               have i₂ := b8e18 (σ X0) (σ X1)
               grind)
            | exact superpose b8e18 b8e19
            | (have j1 := b8e18 (M.op (σ X1) (σ X1)) (σ X1)
               grind)
            | exact resolve b8e19 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e62 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e62
            | (have j0 := b8e62 X0 X1
               grind)
            | exact resolve b8e62 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e77 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e2188 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e71 x y
               grind)
            | exact superpose b8e71 b8e20
            | (have j1 := b8e71 (M.op y y) y
               grind)
            | exact resolve b8e20 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e2235 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e2188
               have r₂ := b8e77
               grind)
            | exact resolve b8e2188 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77 b8e2188
          have b8e2245 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e2235
               have r₂ := b8e23
               grind)
            | exact resolve b8e2235 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2235
          have b8e2261 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e2245
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2245
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | (have r₁ := b8e2245
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e2245
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e2245 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2245
          have b8e2262 : y = (M.op y y) ∨ x = y := by grind
          clear b8e2261
          have b8e2264 : x = y := by
            first
            | (have r₁ := b8e2262
               have r₂ := b8e22
               grind)
            | exact resolve b8e2262 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2262
          have b8e2267 : False := by grind
          exact b8e2267

/-- `Equation4448`: `x ◇ (y ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_x_x_pxy_Equation4448 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4448 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4448.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
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
      have b0e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X0 X3
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e39 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b0e57 X0
           have i₂ := b0e44 X0 y
           grind)
        | exact superpose b0e44 b0e57
        | exact resolve b0e57 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e57
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 X2
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e98 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e58 x
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e58
        | exact resolve b0e58 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e103 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y X1
           have i₂ := b0e58 X0
           grind)
        | exact superpose b0e58 b0e11
        | exact resolve b0e11 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e135 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e36 X0 X1 X2 (M.op y X0)
           have i₂ := b0e58 X0
           grind)
        | exact superpose b0e58 b0e36
        | exact resolve b0e36 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e164 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X2) X3) = (M.op (M.op X0 X2) X3) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = X3 ∨ (M.op X3 (M.op X0 X2)) = X3 := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e16 (M.op X0 X2) X3
           have i₂ := b0e36 X0 X2 (M.op X0 X2) X1
           grind)
        | (have i₁ := b0e16 (M.op X0 X2) X3
           have i₂ := b0e36 X0 X1 (M.op X0 X2) X2
           grind)
        | exact superpose b0e36 b0e16
        | (have j0 := b0e16 (M.op X0 X2) X3
           grind)
        | exact resolve b0e16 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e135 X0 X1 X2
           have i₂ := b0e103 X2 X0
           grind)
        | exact superpose b0e103 b0e135
        | exact resolve b0e135 b0e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103 b0e135
      have b0e208 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op (σ x) X0)
           have i₂ := b0e39 X0
           grind)
        | exact superpose b0e39 b0e11
        | exact resolve b0e11 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e221 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e208 X0 X1
           have i₂ := b0e177 (σ y) X0 X1
           grind)
        | exact superpose b0e177 b0e208
        | exact resolve b0e208 b0e177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e208
      have b0e245 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
        first
        | (have i₁ := b0e221 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e221
        | exact resolve b0e221 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e255 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e39 X0
           have i₂ := b0e221 (σ x) X0
           grind)
        | exact superpose b0e221 b0e39
        | exact resolve b0e39 b0e221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e2162 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e68 X0 X1 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e2163 : ∀ X0 X1 : G, (M.op y X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e2162 X0 X1
           have i₂ := b0e221 X1 X1
           grind)
        | exact superpose b0e221 b0e2162
        | (have j0 := b0e2162 X0 X1
           grind)
        | (have r₁ := b0e2162 (M.op (M.op y y) (M.op X0 (M.op y y))) y
           have r₂ := b0e221 X0 (M.op y y)
           grind)
        | (have r₁ := b0e2162 (M.op y X0) X0
           have r₂ := b0e221 X0 X0
           grind)
        | exact resolve b0e2162 b0e221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e221 b0e2162
      have b0e2354 : (σ (M.op x y)) ≠ (M.op y (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e245
           grind)
        | exact superpose b0e245 b0e18
        | exact resolve b0e18 b0e245
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e245
      have b0e42216 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e164 (σ x) X1 (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e164
        | exact resolve b0e164 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42225 : ∀ X0 X1 : G, (M.op (M.op x X0) y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e164 x X1 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e164
        | exact resolve b0e164 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164
      have b0e42717 : ∀ X1 : G, (M.op y (M.op x y)) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have i₁ := b0e42225 x X1
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e42225
        | (have j0 := b0e42225 x X1
           grind)
        | exact resolve b0e42225 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42225
      have b0e42725 : ∀ X1 : G, (M.op y (σ y)) = X1 ∨ (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have i₁ := b0e42216 x X1
           have i₂ := b0e177 (σ x) x (σ y)
           grind)
        | exact superpose b0e177 b0e42216
        | (have j0 := b0e42216 x X1
           grind)
        | exact resolve b0e42216 b0e177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e177 b0e42216
      have b0e43145 : ∀ X1 : G, (M.op y y) = X1 ∨ (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have i₁ := b0e42717 X1
           have i₂ := b0e40 y
           grind)
        | exact superpose b0e40 b0e42717
        | (have j0 := b0e42717 X1
           grind)
        | exact resolve b0e42717 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e42717
      have b0e43153 : ∀ X1 : G, (M.op (σ y) X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have j0 := b0e42725 X1
           have j1 := b0e2163 X1 (σ y)
           grind)
        | (have r₁ := b0e42725 x
           have r₂ := b0e2163 x (σ y)
           grind)
        | (have r₁ := b0e42725 (M.op y X1)
           have r₂ := b0e2163 (M.op y (σ y)) X1
           grind)
        | (have r₁ := b0e42725 y
           have r₂ := b0e2163 y (σ y)
           grind)
        | exact resolve b0e42725 b0e2163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42725
      have b0e43479 : ∀ X1 : G, (M.op y X1) = (k y X1) ∨ (M.op X1 y) = X1 := by
        intro X1
        first
        | (have j0 := b0e43145 X1
           have j1 := b0e2163 X1 y
           grind)
        | (have r₁ := b0e43145 x
           have r₂ := b0e2163 x y
           grind)
        | (have r₁ := b0e43145 (M.op y X1)
           have r₂ := b0e2163 (M.op y y) X1
           grind)
        | (have r₁ := b0e43145 X1
           have r₂ := b0e2163 (k y X1) X1
           grind)
        | exact resolve b0e43145 b0e2163
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2163 b0e43145
      have b0e43486 : ∀ X1 : G, (M.op y X1) = (k (σ y) X1) ∨ (M.op X1 (σ y)) = X1 := by
        intro X1
        first
        | (have i₁ := b0e43153 X1
           have i₂ := b0e255 X1
           grind)
        | exact superpose b0e255 b0e43153
        | (have j0 := b0e43153 X1
           grind)
        | exact resolve b0e43153 b0e255
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e255 b0e43153
      have b0e44152 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (τ X0) = (M.op (τ X0) y) := by
        intro X0
        first
        | (have i₁ := b0e26 X0 y
           have i₂ := b0e43479 (τ X0)
           grind)
        | exact superpose b0e43479 b0e26
        | (have j1 := b0e43479 (τ X0)
           grind)
        | exact resolve b0e26 b0e43479
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26 b0e43479
      have b0e44362 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ y)) ∨ (M.op y (σ X0)) = (σ (k y X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 y X0
           have i₂ := b0e43486 (σ X0)
           grind)
        | exact superpose b0e43486 b0e17
        | (have j1 := b0e43486 (σ X0)
           grind)
        | exact resolve b0e17 b0e43486
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43486
      have b0e128713 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e44152 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e44152
        | exact resolve b0e44152 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44152
      have b0e128745 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e128713 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e128713
        | (have j0 := b0e128713 X0
           grind)
        | exact resolve b0e128713 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128713
      have b0e128872 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op y (σ x)) = (σ (k y x)) := by
        first
        | (have i₁ := b0e35 (σ y)
           have i₂ := b0e44362 x
           grind)
        | exact superpose b0e44362 b0e35
        | (have j1 := b0e44362 x
           grind)
        | exact resolve b0e35 b0e44362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e44362
      have b0e128991 : (M.op y (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e128872
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e128872
        | exact resolve b0e128872 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128872
      have b0e129044 : (M.op y (σ x)) = (σ (M.op y x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e128745 x
           have i₂ := b0e128991
           grind)
        | exact superpose b0e128991 b0e128745
        | (have j0 := b0e128745 x
           grind)
        | exact resolve b0e128745 b0e128991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e128745 b0e128991
      have b0e129081 : (σ (M.op x y)) = (M.op y (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e129044
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e129044
        | exact resolve b0e129044 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e129044
      have b0e129102 : x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have r₁ := b0e129081
           have r₂ := b0e2354
           grind)
        | exact resolve b0e129081 b0e2354
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2354 b0e129081
      have b0e129120 : x = (M.op x x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e98
           have i₂ := b0e129102
           grind)
        | exact superpose b0e129102 b0e98
        | exact resolve b0e98 b0e129102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98 b0e129102
      have b0e129350 : (σ x) = (σ y) ∨ x = y := by
        first
        | (have i₁ := b0e129120
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e129120
        | exact resolve b0e129120 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129120
      have b0e129451 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e129350
           grind)
        | exact superpose b0e129350 b0e12
        | exact resolve b0e12 b0e129350
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129350
      have b0e129522 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e129451
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e129451
        | exact resolve b0e129451 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129451
      have b0e129523 : x = y := by grind
      clear b0e129522
      have b0e129541 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e129523
           grind)
        | exact superpose b0e129523 b0e18
        | exact resolve b0e18 b0e129523
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129523
      have b0e129928 : (σ y) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e129541
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e129541
        | exact resolve b0e129541 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e129541
      have b0e129995 : False := by grind
      exact b0e129995
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e29 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ x) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X2 X0 X3
             have i₂ := b1e12 X2 X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e33 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e34 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e34 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e34
          | exact resolve b1e34 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e34 X0
             grind)
          | exact superpose b1e34 b1e12
          | exact resolve b1e12 b1e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e34
        have b1e54 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e35
             grind)
          | exact superpose b1e35 b1e12
          | exact resolve b1e12 b1e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e55 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e54 X0
             have i₂ := b1e38 X0 y
             grind)
          | exact superpose b1e38 b1e54
          | exact resolve b1e54 b1e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38 b1e54
        have b1e60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b1e96 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y X1
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e12
          | exact resolve b1e12 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e146 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e30 X0 X1 X2 (M.op y X0)
             have i₂ := b1e55 X0
             grind)
          | exact superpose b1e55 b1e30
          | exact resolve b1e30 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e55
        have b1e189 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e146 X0 X1 X2
             have i₂ := b1e96 X2 X0
             grind)
          | exact superpose b1e96 b1e146
          | exact resolve b1e146 b1e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e96 b1e146
        have b1e228 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e33 (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e33
          | exact resolve b1e33 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e243 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 X0 (M.op (σ y) X0)
             have i₂ := b1e33 X0
             grind)
          | exact superpose b1e33 b1e12
          | exact resolve b1e12 b1e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e258 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e243 X0 X1
             have i₂ := b1e189 (σ y) X0 X1
             grind)
          | exact superpose b1e189 b1e243
          | exact resolve b1e243 b1e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e243
        have b1e270 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e228
             grind)
          | exact superpose b1e228 b1e19
          | exact resolve b1e19 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e298 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) X0) X1) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ x) (M.op (σ y) X0) X1
             have i₂ := b1e29 X0
             grind)
          | exact superpose b1e29 b1e12
          | exact resolve b1e12 b1e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e299 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) X0) X1) (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b1e298 X0 X1
             have i₂ := b1e228
             grind)
          | exact superpose b1e228 b1e298
          | exact resolve b1e298 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e298
        have b1e311 : (M.op (σ x) (σ y)) = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e299 x x
             have i₂ := b1e189 (M.op (σ y) x) x (σ x)
             grind)
          | exact superpose b1e189 b1e299
          | exact resolve b1e299 b1e189
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e189 b1e299
        have b1e319 : (σ y) = (M.op y (σ x)) := by
          first
          | (have i₁ := b1e311
             have i₂ := b1e228
             grind)
          | exact superpose b1e228 b1e311
          | exact resolve b1e311 b1e228
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e228 b1e311
        have b1e3318 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e60 x x
             grind)
          | exact superpose b1e60 b1e21
          | (have j1 := b1e60 x x
             grind)
          | (have r₁ := b1e21
             have r₂ := b1e60 x y
             grind)
          | exact resolve b1e21 b1e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e3423 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b1e3318
        have b1e12467 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e3423
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e3423
          | (have j1 := b1e17 (σ x) (σ x)
             grind)
          | exact resolve b1e3423 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3423
        have b1e12468 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12467
        have b1e12469 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e12468
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12468
          | exact resolve b1e12468 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12468
        have b1e12470 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b1e12469
        have b1e12476 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e12470
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12470
          | exact resolve b1e12470 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12470
        have b1e12521 : (M.op (σ x) (σ x)) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e258 (σ x) (σ x)
             have i₂ := b1e12476
             grind)
          | exact superpose b1e12476 b1e258
          | exact resolve b1e258 b1e12476
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e258 b1e12476
        have b1e12534 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b1e12521
             have i₂ := b1e319
             grind)
          | exact superpose b1e319 b1e12521
          | exact resolve b1e12521 b1e319
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e319 b1e12521
        have b1e12569 : x = y := by
          first
          | (have r₁ := b1e12534
             have r₂ := b1e21
             grind)
          | exact resolve b1e12534 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12534
        have b1e14146 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e270
             have i₂ := b1e12569
             grind)
          | exact superpose b1e12569 b1e270
          | exact resolve b1e270 b1e12569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e270
        have b1e14171 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e14146
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e14146
          | exact resolve b1e14146 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e14146
        have b1e14189 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e14171
             have i₂ := b1e12569
             grind)
          | exact superpose b1e12569 b1e14171
          | exact resolve b1e14171 b1e12569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e12569 b1e14171
        have b1e14190 : False := by grind
        exact b1e14190
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
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
        have b2e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X0 X3
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X3 X2 (M.op X0 X2)
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b2e30 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e30
          | exact resolve b2e30 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op x X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 x X1
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e48 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op (M.op x y) X0) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e12
          | exact resolve b2e12 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e49 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e48 X0
             have i₂ := b2e36 X0 y
             grind)
          | exact superpose b2e36 b2e48
          | exact resolve b2e48 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36 b2e48
        have b2e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b2e59 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
        have b2e90 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y X1
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e12
          | exact resolve b2e12 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e107 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e29 X0 X1 X2 (M.op y X0)
             have i₂ := b2e49 X0
             grind)
          | exact superpose b2e49 b2e29
          | exact resolve b2e29 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49
        have b2e181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e139 X0 X1 X2
             have i₂ := b2e90 X2 X0
             grind)
          | exact superpose b2e90 b2e139
          | exact resolve b2e139 b2e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90 b2e139
        have b2e280 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e29 (M.op X2 X3) X1 X0 X4
             have i₂ := b2e31 X2 X3 X1 X0
             grind)
          | exact superpose b2e31 b2e29
          | exact resolve b2e29 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e31
        have b2e293 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e280 X0 X1 x x x
             have i₂ := b2e181 (M.op x x) x X0
             grind)
          | exact superpose b2e181 b2e280
          | exact resolve b2e280 b2e181
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e280
        have b2e1534 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e107
        have b2e1548 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e1534 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1534
          | exact resolve b2e1534 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1534
        have b2e1552 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have j0 := b2e59 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e1553 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1552
             have r₂ := b2e22
             grind)
          | exact resolve b2e1552 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1552
        have b2e1554 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1553
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1553
          | exact resolve b2e1553 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1553
        have b2e1555 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1554
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1554
          | exact resolve b2e1554 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1554
        have b2e1569 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e181 (σ x) (σ y) X0
             have i₂ := b2e1555
             grind)
          | exact superpose b2e1555 b2e181
          | exact resolve b2e181 b2e1555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e181
        have b2e2251 : (σ x) = (M.op y (σ y)) := by
          first
          | (have i₁ := b2e1555
             have i₂ := b2e1569 (σ y)
             grind)
          | exact superpose b2e1569 b2e1555
          | exact resolve b2e1555 b2e1569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1555
        have b2e2707 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e293 (σ y) y
             have i₂ := b2e2251
             grind)
          | exact superpose b2e2251 b2e293
          | exact resolve b2e293 b2e2251
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e293 b2e2251
        have b2e2771 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e54 x x
             grind)
          | exact superpose b2e54 b2e21
          | (have j1 := b2e54 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e54 x y
             grind)
          | exact resolve b2e21 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e2867 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e2771
        have b2e2933 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y (σ x)) := by
          first
          | (have i₁ := b2e2867
             have i₂ := b2e1569 (σ x)
             grind)
          | exact superpose b2e1569 b2e2867
          | exact resolve b2e2867 b2e1569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2867
        have b2e2995 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e2707
             grind)
          | exact superpose b2e2707 b2e22
          | exact resolve b2e22 b2e2707
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2707
        have b2e3815 : x = (k x (τ (M.op y (σ x)))) := by
          first
          | (have i₁ := b2e1548 x
             have i₂ := b2e1569 (σ x)
             grind)
          | exact superpose b2e1569 b2e1548
          | exact resolve b2e1548 b2e1569
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1548 b2e1569
        have b2e5552 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2933
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e2933
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e2933 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2933
        have b2e5553 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e5552
        have b2e5554 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5553
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5553
          | exact resolve b2e5553 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5553
        have b2e5555 : (σ x) = (M.op y (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e5554
        have b2e5562 : (σ x) = (M.op y (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e5555
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5555
          | exact resolve b2e5555 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5555
        have b2e5567 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3815
             have i₂ := b2e5562
             grind)
          | exact superpose b2e5562 b2e3815
          | exact resolve b2e3815 b2e5562
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3815 b2e5562
        have b2e5620 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e5567
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e5567
          | exact resolve b2e5567 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5567
        have b2e6114 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e5620
             grind)
          | exact superpose b2e5620 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e5620
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5620
        have b2e6115 : x = (M.op x x) ∨ x = y := by grind
        clear b2e6114
        have b2e6122 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e6115
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e6115
          | exact resolve b2e6115 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6115
        have b2e6123 : x = y := by grind
        clear b2e6122
        have b2e6203 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e2995
             have i₂ := b2e6123
             grind)
          | exact superpose b2e6123 b2e2995
          | exact resolve b2e2995 b2e6123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2995 b2e6123
        have b2e6206 : False := by grind
        exact b2e6206
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
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
        have b3e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b3e12 X2 X0 X3
             have i₂ := b3e12 X2 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e46 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : y = (M.op x y) := by
          first
          | (have i₁ := b3e47 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e47
          | exact resolve b3e47 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 y X1
             have i₂ := b3e47 X0
             grind)
          | exact superpose b3e47 b3e12
          | exact resolve b3e12 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e63 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 x y
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e12
          | exact resolve b3e12 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b3e142 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e43 X0 X1 X2 (M.op x X0)
             have i₂ := b3e63 X0
             grind)
          | exact superpose b3e63 b3e43
          | exact resolve b3e43 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e63
        have b3e183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e142 X0 X1 X2
             have i₂ := b3e51 X2 X0
             grind)
          | exact superpose b3e51 b3e142
          | exact resolve b3e142 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e142
        have b3e239 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op (σ y) X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X1 X0 (M.op (σ x) X0)
             have i₂ := b3e46 X0
             grind)
          | exact superpose b3e46 b3e12
          | exact resolve b3e12 b3e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e249 : ∀ X0 X1 : G, (M.op y X1) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e239 X0 X1
             have i₂ := b3e183 (σ y) X0 X1
             grind)
          | exact superpose b3e183 b3e239
          | exact resolve b3e239 b3e183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e183 b3e239
        have b3e3310 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e68 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e68
          | exact resolve b3e68 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e68
        have b3e3420 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e3310
        have b3e4714 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e3420
             grind)
          | exact superpose b3e3420 b3e13
          | exact resolve b3e13 b3e3420
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3420
        have b3e4736 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e4714
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e4714
          | exact resolve b3e4714 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4714
        have b3e4747 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e4736
             grind)
          | exact superpose b3e4736 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e4736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4736
        have b3e4748 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e4747
        have b3e4750 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e4748
             have r₂ := b3e20
             grind)
          | exact resolve b3e4748 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4748
        have b3e5380 : (M.op x x) = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e249 x x
             have i₂ := b3e4750
             grind)
          | exact superpose b3e4750 b3e249
          | exact resolve b3e249 b3e4750
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e249 b3e4750
        have b3e5381 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e5380
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e5380
          | exact resolve b3e5380 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5380
        have b3e5396 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e5381
             have r₂ := b3e20
             grind)
          | exact resolve b3e5381 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5381
        have b3e5566 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e5396
             grind)
          | exact superpose b3e5396 b3e19
          | exact resolve b3e19 b3e5396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e5592 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b3e5566
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e5566
          | exact resolve b3e5566 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5566
        have b3e5597 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e5592
             have i₂ := b3e5396
             grind)
          | exact superpose b3e5396 b3e5592
          | exact resolve b3e5592 b3e5396
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5592
        have b3e5602 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e5597
             have i₂ := b3e48
             grind)
          | exact superpose b3e48 b3e5597
          | exact resolve b3e5597 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e5597
        have b3e5606 : False := by grind
        exact b3e5606
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e34 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op x y) := by
            first
            | (have i₁ := b4e35 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e216 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e34 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e34
            | exact resolve b4e34 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34
          have b4e258 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e216
               grind)
            | exact superpose b4e216 b4e20
            | exact resolve b4e20 b4e216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e216
          have b4e269 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e258
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e258
            | exact resolve b4e258 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e258
          have b4e270 : False := by grind
          exact b4e270
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
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
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e31 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 X2 (M.op X0 X2)
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : y = (M.op x y) := by
            first
            | (have i₁ := b5e31 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e31
            | exact resolve b5e31 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e41 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by
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
          clear b5e41
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e45
               have r₂ := b5e21
               grind)
            | exact resolve b5e45 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b5e55 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 X1)) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X2) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 X2
               have i₂ := b5e18 X2 X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op X1 X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X2 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X1 X2) X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X1 X2
               have i₂ := b5e18 X1 X0
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
          have b5e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b5e59 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e34
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e65 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e129 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X2 X3) X4) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e30 X2 X3 X4 (M.op X0 X2)
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e30
            | exact resolve b5e30 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e131 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e30 X0 X1 X2 (M.op x X0)
               have i₂ := b5e59 X0
               grind)
            | exact superpose b5e59 b5e30
            | exact resolve b5e30 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e171 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e131 X0 X1 X2
               have i₂ := b5e37 X2 X0
               grind)
            | exact superpose b5e37 b5e131
            | exact resolve b5e131 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e131
          have b5e272 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e30 (M.op X2 X3) X1 X0 X4
               have i₂ := b5e32 X2 X3 X1 X0
               grind)
            | exact superpose b5e32 b5e30
            | exact resolve b5e30 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e32
          have b5e275 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e272 X0 X1 x x x
               have i₂ := b5e171 (M.op x x) x X0
               grind)
            | exact superpose b5e171 b5e272
            | exact resolve b5e272 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e272
          have b5e1600 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b5e57 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e1601 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1600
               have r₂ := b5e24
               grind)
            | exact resolve b5e1600 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1600
          have b5e1602 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1601
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1601
            | exact resolve b5e1601 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1601
          have b5e1603 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1602
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e1602
            | exact resolve b5e1602 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e1602
          have b5e1604 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1603
               grind)
            | exact superpose b5e1603 b5e20
            | exact resolve b5e20 b5e1603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1617 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e171 (σ x) (σ y) X0
               have i₂ := b5e1603
               grind)
            | exact superpose b5e1603 b5e171
            | exact resolve b5e171 b5e1603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1603
          have b5e1632 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b5e1604
               have i₂ := b5e34
               grind)
            | exact superpose b5e34 b5e1604
            | exact resolve b5e1604 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e1604
          have b5e1760 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) X2) = (M.op X2 (M.op (σ X0) X2)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e55 (σ X1) X2 (σ X0)
               grind)
            | exact superpose b5e55 b5e19
            | (have j1 := b5e55 (σ X1) X2 (σ X0)
               grind)
            | exact resolve b5e19 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1762 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e55 X0 X1 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e1763 : ∀ X0 X1 : G, (M.op y X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e1762 X0 X1
               have i₂ := b5e275 X1 X1
               grind)
            | exact superpose b5e275 b5e1762
            | (have j0 := b5e1762 X0 X1
               grind)
            | (have r₁ := b5e1762 (M.op y X1) X1
               have r₂ := b5e275 X1 X1
               grind)
            | (have r₁ := b5e1762 (M.op (M.op y y) (M.op X1 (M.op y y))) y
               have r₂ := b5e275 (M.op y y) X1
               grind)
            | exact resolve b5e1762 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1762
          have b5e1765 : ∀ X0 X1 X2 : G, (M.op y X2) = (M.op (σ X1) X2) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1760 X0 X1 X2
               have i₂ := b5e275 X2 (σ X0)
               grind)
            | exact superpose b5e275 b5e1760
            | (have j0 := b5e1760 X0 X1 X2
               grind)
            | exact resolve b5e1760 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1760
          have b5e2072 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X0) X2) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e19 X0 X1
               have i₂ := b5e56 (σ X1) (σ X0) X2
               grind)
            | exact superpose b5e56 b5e19
            | (have j1 := b5e56 (σ X1) (σ X0) X2
               grind)
            | exact resolve b5e19 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2076 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op y (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2072 X0 X1 x
               have i₂ := b5e171 (σ X0) x (σ X0)
               grind)
            | exact superpose b5e171 b5e2072
            | (have j0 := b5e2072 X0 X1 x
               grind)
            | exact resolve b5e2072 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2072
          have b5e2853 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ X0)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e51 X2 X0
               have i₂ := b5e56 (σ X2) (σ X0) X1
               grind)
            | exact superpose b5e56 b5e51
            | (have j0 := b5e51 X2 X0
               have j1 := b5e56 (σ X2) (σ X0) X2
               grind)
            | exact resolve b5e51 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e2919 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e51 X1 X0
               grind)
            | exact superpose b5e51 b5e17
            | (have j0 := b5e17 (σ X1) (σ X0)
               have j1 := b5e51 X1 X0
               grind)
            | (have r₁ := b5e17 (σ X1) (σ X1)
               have r₂ := b5e51 X1 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e51 X0 X1
               grind)
            | exact resolve b5e17 b5e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e2944 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e2919 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2919
          have b5e2945 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e2944 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2944
          have b5e2972 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2945 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e2945
            | (have j0 := b5e2945 X0 X1
               grind)
            | exact resolve b5e2945 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2945
          have b5e3018 : ∀ X0 X2 : G, (σ X0) = (M.op y (σ X0)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (M.op (σ X0) (σ X2)) = (k (σ X0) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
            intro X0 X2
            first
            | (have i₁ := b5e2853 X0 x X2
               have i₂ := b5e171 (σ X0) x (σ X0)
               grind)
            | exact superpose b5e171 b5e2853
            | (have j0 := b5e2853 X0 x X2
               grind)
            | exact resolve b5e2853 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2853
          have b5e3057 : ∀ X0 X2 : G, (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (M.op (σ X2) (σ X0)) = (σ (k X2 X0)) ∨ (σ X0) = (M.op (σ X2) (σ X2)) ∨ (σ X0) = (M.op y (σ X0)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
            intro X0 X2
            first
            | (have i₁ := b5e3018 X0 X2
               have i₂ := b5e19 X0 X2
               grind)
            | exact superpose b5e19 b5e3018
            | (have j0 := b5e3018 X0 X2
               grind)
            | exact resolve b5e3018 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3018
          have b5e4478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X4 ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op X4 (M.op X2 X3)) = X4 := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e18 (M.op X2 X3) X4
               have i₂ := b5e129 X0 X1 X2 X3 (M.op X2 X3)
               grind)
            | (have i₁ := b5e18 (M.op (M.op X0 X1) X2) X1
               have i₂ := b5e129 X0 X1 X2 X3 (M.op (M.op X0 X1) X2)
               grind)
            | exact superpose b5e129 b5e18
            | (have j0 := b5e18 (M.op X2 X3) X4
               grind)
            | exact resolve b5e18 b5e129
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129
          have b5e4580 : ∀ X2 X3 X4 : G, (M.op y (M.op X2 X3)) = X4 ∨ (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op X4 (M.op X2 X3)) = X4 := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e4478 x x X2 X3 X4
               have i₂ := b5e171 (M.op x x) X2 (M.op X2 X3)
               grind)
            | exact superpose b5e171 b5e4478
            | (have j0 := b5e4478 x x X2 X3 X4
               grind)
            | exact resolve b5e4478 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4478
          have b5e4743 : ∀ X2 X3 X4 : G, (M.op (M.op X2 X3) X4) = (k (M.op X2 X3) X4) ∨ (M.op X4 (M.op X2 X3)) = X4 := by
            intro X2 X3 X4
            first
            | (have j0 := b5e4580 X2 X3 X4
               have j1 := b5e1763 X4 (M.op X2 X3)
               grind)
            | (have r₁ := b5e4580 X2 X3 x
               have r₂ := b5e1763 x (M.op X2 X3)
               grind)
            | (have r₁ := b5e4580 X2 X3 (M.op y x)
               have r₂ := b5e1763 (M.op y (M.op X2 X3)) x
               grind)
            | (have r₁ := b5e4580 X2 X3 y
               have r₂ := b5e1763 y (M.op X2 X3)
               grind)
            | exact resolve b5e4580 b5e1763
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1763 b5e4580
          have b5e4799 : ∀ X2 X3 X4 : G, (M.op y X4) = (k (M.op X2 X3) X4) ∨ (M.op X4 (M.op X2 X3)) = X4 := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e4743 X2 X3 X4
               have i₂ := b5e171 X2 X3 X4
               grind)
            | exact superpose b5e171 b5e4743
            | (have j0 := b5e4743 X2 X3 X4
               grind)
            | exact resolve b5e4743 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4743
          have b5e32407 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b5e2972
          have b5e32521 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e32407 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e32407
            | (have j0 := b5e32407 X0 X1
               grind)
            | exact resolve b5e32407 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32407
          have b5e32522 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e32521 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32521
          have b5e33171 : ∀ X0 X1 : G, (σ X0) ≠ (M.op y (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e1765 X1 X0 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1765
          have b5e38747 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op y (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op y (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e275 (σ X1) (σ X0)
               have i₂ := b5e2076 X1 X0
               grind)
            | exact superpose b5e2076 b5e275
            | (have j1 := b5e2076 X1 X0
               grind)
            | exact resolve b5e275 b5e2076
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2076
          have b5e38781 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op y (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e38747 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38747
          have b5e70964 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e32522 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e32522
            | exact resolve b5e32522 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32522
          have b5e71262 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e70964 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e70964
            | (have j0 := b5e70964 X0 X1
               grind)
            | exact resolve b5e70964 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70964
          have b5e71290 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e71262 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e71262
            | (have j0 := b5e71262 X0 X1
               grind)
            | exact resolve b5e71262 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71262
          have b5e75551 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e71290 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e71290
            | exact resolve b5e71290 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71290
          have b5e76372 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e75551 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75551
          have b5e77034 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op y X0) ∨ (M.op X1 X2) = (k (M.op X1 X2) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e76372 (M.op X1 X2) X0
               have i₂ := b5e171 X1 X2 X0
               grind)
            | exact superpose b5e171 b5e76372
            | (have j0 := b5e76372 (M.op X1 X2) X0
               grind)
            | (have r₁ := b5e76372 (M.op y X2) X2
               have r₂ := b5e171 y X2 X2
               grind)
            | exact resolve b5e76372 b5e171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e171 b5e76372
          have b5e94901 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e3057 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3057
          have b5e94905 : ∀ X0 : G, (σ (k X0 X0)) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e94901 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94901
          have b5e94906 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e94905 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94905
          have b5e95041 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e94906 X0
               have j1 := b5e33171 X0 X0
               grind)
            | (have r₁ := b5e94906 x
               have r₂ := b5e33171 x x
               grind)
            | exact resolve b5e94906 b5e33171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33171 b5e94906
          have b5e100171 : (M.op y (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e95041 x
               have i₂ := b5e1617 (σ x)
               grind)
            | exact superpose b5e1617 b5e95041
            | exact resolve b5e95041 b5e1617
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1617 b5e95041
          have b5e102466 : (k x x) = (τ (M.op y (σ x))) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e100171
               grind)
            | exact superpose b5e100171 b5e14
            | exact resolve b5e14 b5e100171
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100171
          have b5e103579 : ∀ X0 : G, (M.op y X0) = (k (M.op y X0) X0) := by
            intro X0
            first
            | (have j0 := b5e77034 X0 y X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e103759 : ∀ X0 : G, (τ (M.op y (σ X0))) = (k (τ (M.op y (σ X0))) X0) := by
            intro X0
            first
            | (have i₁ := b5e65 (M.op y (σ X0)) X0
               have i₂ := b5e103579 (σ X0)
               grind)
            | exact superpose b5e103579 b5e65
            | exact resolve b5e65 b5e103579
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e103579
          have b5e104783 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op y X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e38781 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e38781
            | exact resolve b5e38781 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38781
          have b5e104905 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op y X0) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e104783 X0 X1
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e104783
            | (have j0 := b5e104783 X0 X1
               grind)
            | exact resolve b5e104783 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e104783
          have b5e106529 : (k x x) = (k (k x x) x) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e103759 x
               have i₂ := b5e102466
               grind)
            | exact superpose b5e102466 b5e103759
            | exact resolve b5e103759 b5e102466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102466
          have b5e111903 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e104905 X0 (τ X0)
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e104905
            | exact resolve b5e104905 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104905
          have b5e112153 : (M.op x x) = (k (M.op x x) x) ∨ (σ x) = (M.op y (σ x)) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e106529
               have i₂ := b5e111903 x x
               grind)
            | exact superpose b5e111903 b5e106529
            | (have j1 := b5e111903 x x
               grind)
            | exact resolve b5e106529 b5e111903
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106529 b5e111903
          have b5e112189 : (M.op x x) = (k (M.op x x) x) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have j1 := b5e77034 x x x
               grind)
            | (have r₁ := b5e112153
               have r₂ := b5e77034 x x x
               grind)
            | exact resolve b5e112153 b5e77034
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77034 b5e112153
          have b5e113038 : (M.op x x) = (M.op y x) ∨ x = (M.op x (M.op x x)) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e4799 x x x
               have i₂ := b5e112189
               grind)
            | exact superpose b5e112189 b5e4799
            | (have j0 := b5e4799 x x x
               grind)
            | exact resolve b5e4799 b5e112189
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4799 b5e112189
          have b5e113039 : y = (M.op x x) ∨ x = (M.op x (M.op x x)) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e113038
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e113038
            | exact resolve b5e113038 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113038
          have b5e113041 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have r₁ := b5e113039
               have r₂ := b5e21
               grind)
            | exact resolve b5e113039 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113039
          have b5e113043 : x = (M.op y x) ∨ (σ x) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e113041
               have i₂ := b5e275 x x
               grind)
            | exact superpose b5e275 b5e113041
            | exact resolve b5e113041 b5e275
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113041
          have b5e113045 : (σ x) = (M.op y (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e113043
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e113043
            | exact resolve b5e113043 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113043
          have b5e113073 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = y := by
            first
            | (have i₁ := b5e103759 x
               have i₂ := b5e113045
               grind)
            | exact superpose b5e113045 b5e103759
            | exact resolve b5e103759 b5e113045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103759 b5e113045
          have b5e113271 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e113073
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e113073
            | exact resolve b5e113073 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113073
          have b5e113374 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e18 x x
               have i₂ := b5e113271
               grind)
            | exact superpose b5e113271 b5e18
            | (have j0 := b5e18 x x
               grind)
            | exact resolve b5e18 b5e113271
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113271
          have b5e113386 : x = (M.op x x) ∨ x = y := by grind
          clear b5e113374
          have b5e113524 : (M.op x x) = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b5e275 x x
               have i₂ := b5e113386
               grind)
            | exact superpose b5e113386 b5e275
            | exact resolve b5e275 b5e113386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e275 b5e113386
          have b5e113590 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b5e113524
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e113524
            | exact resolve b5e113524 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113524
          have b5e113648 : x = y := by
            first
            | (have r₁ := b5e113590
               have r₂ := b5e21
               grind)
            | exact resolve b5e113590 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e113590
          have b5e113786 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1632
               have i₂ := b5e113648
               grind)
            | exact superpose b5e113648 b5e1632
            | exact resolve b5e1632 b5e113648
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1632 b5e113648
          have b5e113983 : False := by grind
          exact b5e113983
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
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
        have b6e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
        have b6e76 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
        have b6e84 : x = (M.op x y) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e76
             have r₂ := b6e20
             grind)
          | exact resolve b6e76 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e87 : x = (M.op x y) := by
          first
          | (have r₁ := b6e84
             have r₂ := b6e21
             grind)
          | exact resolve b6e84 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e90 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e12
          | exact resolve b6e12 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e158 : x = (M.op y x) := by
          first
          | (have i₁ := b6e90 y
             have i₂ := b6e87
             grind)
          | exact superpose b6e87 b6e90
          | exact resolve b6e90 b6e87
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87 b6e90
        have b6e210 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e158
             grind)
          | exact superpose b6e158 b6e21
          | exact resolve b6e21 b6e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e158
        have b6e3061 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e74 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e74
          | exact resolve b6e74 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e3171 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3061
        have b6e5533 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3171
             grind)
          | exact superpose b6e3171 b6e13
          | exact resolve b6e13 b6e3171
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5555 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e5533
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e5533
          | exact resolve b6e5533 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5533
        have b6e5566 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e5555
             grind)
          | exact superpose b6e5555 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e5555
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5555
        have b6e5567 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e5566
        have b6e5569 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e5567
             have r₂ := b6e20
             grind)
          | exact resolve b6e5567 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5567
        have b6e6256 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e5569
        have b6e6391 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3171
             have i₂ := b6e6256
             grind)
          | exact superpose b6e6256 b6e3171
          | exact resolve b6e3171 b6e6256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3171 b6e6256
        have b6e6398 : (σ x) = (σ y) := by grind
        clear b6e6391
        have b6e6604 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e6398
             grind)
          | exact superpose b6e6398 b6e13
          | exact resolve b6e13 b6e6398
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6398
        have b6e6623 : x = y := by
          first
          | (have i₁ := b6e6604
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e6604
          | exact resolve b6e6604 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6604
        have b6e6631 : False := by grind
        exact b6e6631
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
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
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b7e28 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
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
          have b7e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X2 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op X1 X2) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X0 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e32 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e33 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 (M.op X0 X2)
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e44 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e41
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
          have b7e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
          have b7e66 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
          have b7e67 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e21
               grind)
            | exact resolve b7e66 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : x = (M.op x y) := by
            first
            | (have r₁ := b7e67
               have r₂ := b7e22
               grind)
            | exact resolve b7e67 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e81 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e13
            | exact resolve b7e13 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e100 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 (σ y) X0 X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e31
            | exact resolve b7e31 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e101 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e31 x X0 X1 y
               have i₂ := b7e69
               grind)
            | exact superpose b7e69 b7e31
            | exact resolve b7e31 b7e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e127 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e32 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e32
            | exact resolve b7e32 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e136 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e31 X0 (M.op (σ y) X0) X1 X2
               have i₂ := b7e32 X0
               grind)
            | exact superpose b7e32 b7e31
            | exact resolve b7e31 b7e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e145 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e136 X0 X1 X2
               have i₂ := b7e100 X0 X1
               grind)
            | exact superpose b7e100 b7e136
            | exact resolve b7e136 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100 b7e136
          have b7e226 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 (M.op X2 X3) X3 X4
               have i₂ := b7e33 X0 X1 X2 X3
               grind)
            | exact superpose b7e33 b7e13
            | exact resolve b7e13 b7e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e252 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (σ y) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e226 X0 X1 X2 X3 x
               have i₂ := b7e145 X3 (M.op X2 X3) x
               grind)
            | exact superpose b7e145 b7e226
            | exact resolve b7e226 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e226
          have b7e278 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op (σ y) (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e252 X0 X1 X2 X3
               have i₂ := b7e145 X2 (M.op (M.op (M.op X0 X1) X2) X3) X3
               grind)
            | exact superpose b7e145 b7e252
            | exact resolve b7e252 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e252
          have b7e287 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op (σ y) (M.op (σ y) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e278 x x X2 X3
               have i₂ := b7e145 (M.op x x) X3 X2
               grind)
            | exact superpose b7e145 b7e278
            | exact resolve b7e278 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e278
          have b7e298 : ∀ X0 X1 X2 : G, (M.op x X0) = (M.op (M.op (M.op X1 X2) x) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e33 X1 X2 x X0
               have i₂ := b7e81 X0
               grind)
            | exact superpose b7e81 b7e33
            | exact resolve b7e33 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e300 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e28 (M.op x (σ y))
               have i₂ := b7e81 (σ y)
               grind)
            | exact superpose b7e81 b7e28
            | exact resolve b7e28 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e322 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ x))) := by
            first
            | (have i₁ := b7e300
               have i₂ := b7e13 (σ x) x (σ y)
               grind)
            | exact superpose b7e13 b7e300
            | exact resolve b7e300 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e300
          have b7e323 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e298 X0 x x
               have i₂ := b7e145 (M.op x x) X0 x
               grind)
            | exact superpose b7e145 b7e298
            | exact resolve b7e298 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e298
          have b7e331 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e322
               have i₂ := b7e81 (σ x)
               grind)
            | exact superpose b7e81 b7e322
            | exact resolve b7e322 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e322
          have b7e336 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e331
               have i₂ := b7e127
               grind)
            | exact superpose b7e127 b7e331
            | exact resolve b7e331 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127 b7e331
          have b7e897 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X4)) = (M.op (M.op X3 X4) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e29 X3 (M.op X3 (M.op X0 X3)) X4 X5
               have i₂ := b7e30 X3 X0 X1 X2
               grind)
            | exact superpose b7e30 b7e29
            | exact resolve b7e29 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e30
          have b7e1022 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X4)) = (M.op (σ y) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4)) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b7e897 X0 X1 X2 X3 X4 X5
               have i₂ := b7e145 X3 (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X4
               grind)
            | exact superpose b7e145 b7e897
            | exact resolve b7e897 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e897
          have b7e1113 : ∀ X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X4)) = (M.op (σ y) (M.op (σ y) X4)) := by
            intro X3 X4 X5
            first
            | (have i₁ := b7e1022 x x x X3 X4 X5
               have i₂ := b7e287 (M.op (M.op (M.op x x) x) X3) X4
               grind)
            | exact superpose b7e287 b7e1022
            | exact resolve b7e1022 b7e287
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e287 b7e1022
          have b7e1195 : ∀ X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X4)) = (M.op x (M.op (σ y) X4)) := by
            intro X3 X4 X5
            first
            | (have i₁ := b7e1113 X3 X4 X5
               have i₂ := b7e323 (M.op (σ y) X4)
               grind)
            | exact superpose b7e323 b7e1113
            | exact resolve b7e1113 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1113
          have b7e1262 : ∀ X3 X4 X5 : G, (M.op (M.op X4 X5) (M.op X3 X4)) = (M.op x (M.op x X4)) := by
            intro X3 X4 X5
            first
            | (have i₁ := b7e1195 X3 X4 X5
               have i₂ := b7e323 X4
               grind)
            | exact superpose b7e323 b7e1195
            | exact resolve b7e1195 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1195
          have b7e1307 : ∀ X3 X4 : G, (M.op (σ y) (M.op X3 X4)) = (M.op x (M.op x X4)) := by
            intro X3 X4
            first
            | (have i₁ := b7e1262 X3 X4 x
               have i₂ := b7e145 X4 (M.op X3 X4) x
               grind)
            | exact superpose b7e145 b7e1262
            | exact resolve b7e1262 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1262
          have b7e1335 : ∀ X3 X4 : G, (M.op x (M.op x X4)) = (M.op x (M.op X3 X4)) := by
            intro X3 X4
            first
            | (have i₁ := b7e1307 X3 X4
               have i₂ := b7e323 (M.op X3 X4)
               grind)
            | exact superpose b7e323 b7e1307
            | exact resolve b7e1307 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1307
          have b7e3482 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e17 (σ X1) (σ X0)
               have i₂ := b7e55 X1 X0
               grind)
            | exact superpose b7e55 b7e17
            | (have j0 := b7e17 (σ X1) (σ X0)
               have j1 := b7e55 X1 X0
               grind)
            | (have r₁ := b7e17 (σ X1) (σ X1)
               have r₂ := b7e55 X1 X1
               grind)
            | (have r₁ := b7e17 (σ X0) (σ X1)
               have r₂ := b7e55 X0 X1
               grind)
            | exact resolve b7e17 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e3489 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X2) = (M.op (M.op (σ X0) X1) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (M.op (σ X3) (σ X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e31 (σ X0) X1 X2 (σ X3)
               have i₂ := b7e55 X3 X0
               grind)
            | exact superpose b7e55 b7e31
            | (have j1 := b7e55 X3 X0
               grind)
            | exact resolve b7e31 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e3503 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e55 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e3504 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e3503 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3503
          have b7e3506 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e3482 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3482
          have b7e3507 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e3506 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3506
          have b7e3527 : ∀ X0 X2 X3 : G, (M.op (σ y) X2) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (M.op (σ X3) (σ X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e3489 X0 x X2 X3
               have i₂ := b7e145 (σ X0) X2 x
               grind)
            | exact superpose b7e145 b7e3489
            | (have j0 := b7e3489 X0 x X2 X3
               grind)
            | exact resolve b7e3489 b7e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3489
          have b7e3534 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e3507 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e3507
            | (have j0 := b7e3507 X0 X1
               grind)
            | exact resolve b7e3507 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3507
          have b7e3615 : ∀ X0 X2 X3 : G, (M.op x X2) = (M.op (σ X0) X2) ∨ (σ (k X3 X0)) = (M.op (σ X3) (σ X0)) ∨ (σ X0) = (M.op (σ X3) (σ X3)) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e3527 X0 X2 X3
               have i₂ := b7e323 X2
               grind)
            | exact superpose b7e323 b7e3527
            | (have j0 := b7e3527 X0 X2 X3
               grind)
            | exact resolve b7e3527 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3527
          have b7e3750 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op (σ y) (M.op X0 X1))) := by
            intro X0 X1
            grind
          have b7e3836 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op x (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e3750 X0 X1
               have i₂ := b7e323 (M.op X0 X1)
               grind)
            | exact superpose b7e323 b7e3750
            | exact resolve b7e3750 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3750
          have b7e4216 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op x (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e1335 X2 X1
               have i₂ := b7e1335 X0 X1
               grind)
            | (have i₁ := b7e1335 x x
               have i₂ := b7e1335 x x
               grind)
            | exact superpose b7e1335 b7e1335
            | exact resolve b7e1335 b7e1335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1335
          have b7e8868 : (M.op x x) = (k (M.op x x) (M.op x x)) := by
            first
            | (have i₁ := b7e3836 x x
               have i₂ := b7e81 x
               grind)
            | exact superpose b7e81 b7e3836
            | exact resolve b7e3836 b7e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81 b7e3836
          have b7e10939 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e3504 (M.op x x)
               have i₂ := b7e8868
               grind)
            | exact superpose b7e8868 b7e3504
            | (have j0 := b7e3504 (M.op x x)
               grind)
            | exact resolve b7e3504 b7e8868
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3504 b7e8868
          have b7e10945 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ (M.op x x))) := by grind
          clear b7e10939
          have b7e23261 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e145 (σ (M.op x x)) X0 (σ (M.op x x))
               have i₂ := b7e10945
               grind)
            | exact superpose b7e10945 b7e145
            | exact resolve b7e145 b7e10945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e145
          have b7e23271 : ∀ X0 : G, (M.op x (σ (M.op x x))) = (M.op x (M.op X0 (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b7e4216 X0 (σ (M.op x x)) (σ (M.op x x))
               have i₂ := b7e10945
               grind)
            | exact superpose b7e10945 b7e4216
            | exact resolve b7e4216 b7e10945
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4216
          have b7e23281 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x x)) X0) := by
            intro X0
            first
            | (have i₁ := b7e23261 X0
               have i₂ := b7e323 X0
               grind)
            | exact superpose b7e323 b7e23261
            | exact resolve b7e23261 b7e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e323 b7e23261
          have b7e24212 : (σ (M.op x x)) = (M.op x (σ (M.op x x))) := by
            first
            | (have i₁ := b7e10945
               have i₂ := b7e23281 (σ (M.op x x))
               grind)
            | exact superpose b7e23281 b7e10945
            | exact resolve b7e10945 b7e23281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e10945
          have b7e41275 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            grind
          clear b7e3534
          have b7e41394 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b7e41275 X0 X1
               have i₂ := b7e19 X1 X0
               grind)
            | exact superpose b7e19 b7e41275
            | (have j0 := b7e41275 X0 X1
               grind)
            | exact resolve b7e41275 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41275
          have b7e41395 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b7e41394 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41394
          have b7e45868 : ∀ X0 : G, (σ y) ≠ (M.op x (σ x)) ∨ (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e23
               have i₂ := b7e3615 x (σ x) X0
               grind)
            | exact superpose b7e3615 b7e23
            | (have j1 := b7e3615 x x X0
               grind)
            | (have r₁ := b7e23
               have r₂ := b7e3615 y x x
               grind)
            | exact resolve b7e23 b7e3615
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3615
          have b7e46363 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b7e45868 X0
               grind)
            | (have r₁ := b7e45868 X0
               have r₂ := b7e336
               grind)
            | exact resolve b7e45868 b7e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45868
          have b7e53382 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e41395 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e41395
            | exact resolve b7e41395 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41395
          have b7e53672 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e53382 X0 X1
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e53382
            | (have j0 := b7e53382 X0 X1
               grind)
            | exact resolve b7e53382 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53382
          have b7e53726 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e53672 X0 X1
               have i₂ := b7e26 X0 X1
               grind)
            | exact superpose b7e26 b7e53672
            | (have j0 := b7e53672 X0 X1
               grind)
            | exact resolve b7e53672 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e53672
          have b7e59122 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e53726 X0 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e53726
            | exact resolve b7e53726 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53726
          have b7e59699 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b7e59122 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59122
          have b7e60312 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ (M.op x X1) = (k (M.op x X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e59699 (M.op x X1) X0
               have i₂ := b7e101 X1 X0
               grind)
            | exact superpose b7e101 b7e59699
            | (have j0 := b7e59699 (M.op x X1) X0
               grind)
            | (have r₁ := b7e59699 (M.op x X1) X1
               have r₂ := b7e101 X1 X1
               grind)
            | exact resolve b7e59699 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101 b7e59699
          have b7e93805 : ∀ X0 : G, (M.op x X0) = (k (M.op x X0) X0) := by
            intro X0
            first
            | (have j0 := b7e60312 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60312
          have b7e111238 : (M.op x (σ x)) = (M.op x (σ (M.op x x))) ∨ (M.op (σ (M.op x x)) (σ x)) = (σ (k (M.op x x) x)) := by
            first
            | (have i₁ := b7e23271 (σ (M.op x x))
               have i₂ := b7e46363 (M.op x x)
               grind)
            | exact superpose b7e46363 b7e23271
            | (have j1 := b7e46363 (M.op x x)
               grind)
            | exact resolve b7e23271 b7e46363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23271 b7e46363
          have b7e111367 : (M.op x (σ x)) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ x)) = (σ (k (M.op x x) x)) := by
            first
            | (have i₁ := b7e111238
               have i₂ := b7e24212
               grind)
            | exact superpose b7e24212 b7e111238
            | exact resolve b7e111238 b7e24212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e24212 b7e111238
          have b7e111467 : (σ y) = (σ (M.op x x)) ∨ (M.op (σ (M.op x x)) (σ x)) = (σ (k (M.op x x) x)) := by
            first
            | (have i₁ := b7e111367
               have i₂ := b7e336
               grind)
            | exact superpose b7e336 b7e111367
            | exact resolve b7e111367 b7e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111367
          have b7e111512 : (σ (M.op x x)) = (M.op (σ (M.op x x)) (σ x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e111467
               have i₂ := b7e93805 x
               grind)
            | exact superpose b7e93805 b7e111467
            | exact resolve b7e111467 b7e93805
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93805 b7e111467
          have b7e111532 : (M.op x (σ x)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e111512
               have i₂ := b7e23281 (σ x)
               grind)
            | exact superpose b7e23281 b7e111512
            | exact resolve b7e111512 b7e23281
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e23281 b7e111512
          have b7e111542 : (σ y) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e111532
               have i₂ := b7e336
               grind)
            | exact superpose b7e336 b7e111532
            | exact resolve b7e111532 b7e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e336 b7e111532
          have b7e111543 : (σ y) = (σ (M.op x x)) := by grind
          clear b7e111542
          have b7e111552 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e111543
               grind)
            | exact superpose b7e111543 b7e14
            | exact resolve b7e14 b7e111543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111543
          have b7e111659 : y = (M.op x x) := by
            first
            | (have i₁ := b7e111552
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e111552
            | exact resolve b7e111552 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111552
          have b7e111675 : False := by grind
          exact b7e111675
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
          have b8e58 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 (σ x)) = X0 := by
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
          have b8e739 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have j0 := b8e58 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e740 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e739
               have r₂ := b8e24
               grind)
            | exact resolve b8e739 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e739
          have b8e741 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e740
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e740
            | exact resolve b8e740 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e740
          have b8e742 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e741
               grind)
            | exact superpose b8e741 b8e20
            | exact resolve b8e20 b8e741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e741
          have b8e884 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e742
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e742
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e742 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e742
          have b8e885 : y = (M.op x x) ∨ y = (M.op y x) := by grind
          clear b8e884
          have b8e887 : y = (M.op y x) := by
            first
            | (have r₁ := b8e885
               have r₂ := b8e21
               grind)
            | exact resolve b8e885 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e885
          have b8e889 : False := by grind
          exact b8e889

/-- `Equation4448`: `x ◇ (y ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_x_pxy_Equation4448 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4448 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4448.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op a b :=
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
      have b0e62 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e65 : False := by grind
      exact b0e65
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e38 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : y = (M.op x y) := by
            first
            | (have i₁ := b4e39 x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e39
            | exact resolve b4e39 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e222 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e38 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e38
            | exact resolve b4e38 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e264 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e222
               grind)
            | exact superpose b4e222 b4e20
            | exact resolve b4e20 b4e222
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e222
          have b4e274 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b4e264
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e264
            | exact resolve b4e264 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e264
          have b4e275 : False := by grind
          exact b4e275
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
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
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X0 X2)) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X2) X2 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X0 X3
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X3 X2 (M.op X0 X2)
               have i₂ := b5e13 X2 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : y = (M.op x y) := by
            first
            | (have i₁ := b5e35 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op y X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 : G, (M.op (M.op y X0) X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 X0 (M.op y X0)
               have i₂ := b5e35 X0
               grind)
            | exact superpose b5e35 b5e13
            | exact resolve b5e13 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e45 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e48 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e17 X0 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e17
            | (have j0 := b5e17 (M.op X1 X2) X0
               grind)
            | (have r₁ := b5e17 X0 (M.op X0 (M.op X0 X0))
               have r₂ := b5e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b5e17 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : x = y ∨ x = (k x y) := by grind
          clear b5e45
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
          have b5e53 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b5e56 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x y
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e13
            | exact resolve b5e13 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e58 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          have b5e59 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e26 X0 X1
               have i₂ := b5e18 (τ X0) X1
               grind)
            | exact superpose b5e18 b5e26
            | (have j1 := b5e18 (τ X0) X1
               grind)
            | exact resolve b5e26 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e62 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e14 (k (τ X0) X1)
               have i₂ := b5e26 X0 X1
               grind)
            | exact superpose b5e26 b5e14
            | exact resolve b5e14 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26
          have b5e63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b5e58 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e58
            | exact resolve b5e58 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e58
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            grind
          clear b5e63
          have b5e74 : ∀ X0 : G, (M.op y (M.op y X0)) = (M.op y (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e35 (M.op y X0)
               have i₂ := b5e41 (M.op y (M.op y X0)) X0
               grind)
            | exact superpose b5e41 b5e35
            | exact resolve b5e35 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e111 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e112 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) (σ X0) X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e13
            | exact resolve b5e13 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e149 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e34 X0 X1 X2 (M.op x X0)
               have i₂ := b5e56 X0
               grind)
            | exact superpose b5e56 b5e34
            | exact resolve b5e34 b5e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e192 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op y X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e149 X0 X1 X2
               have i₂ := b5e41 X2 X0
               grind)
            | exact superpose b5e41 b5e149
            | exact resolve b5e149 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e149
          have b5e222 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op (M.op X1 X2) (σ X0)) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e36 X1 X2 (σ X0) (σ X0)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e36
            | exact resolve b5e36 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e261 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e13 (M.op X2 X3) X3 X4
               have i₂ := b5e36 X0 X1 X2 X3
               grind)
            | exact superpose b5e36 b5e13
            | exact resolve b5e13 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e267 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op (M.op X3 X5) (M.op X2 (M.op X3 X4))) := by
            intro X0 X1 X2 X3 X4 X5
            first
            | (have i₁ := b5e34 X3 X4 (M.op X2 (M.op X3 X4)) X5
               have i₂ := b5e36 X0 X1 X2 (M.op X3 X4)
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e271 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op (M.op X2 X3) X4) X0) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e34 (M.op X2 X3) X1 X0 X4
               have i₂ := b5e36 X2 X3 X1 X0
               grind)
            | exact superpose b5e36 b5e34
            | exact resolve b5e34 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e36
          have b5e284 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e271 X0 X1 x x x
               have i₂ := b5e192 (M.op x x) x X0
               grind)
            | exact superpose b5e192 b5e271
            | exact resolve b5e271 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e271
          have b5e288 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X3 X4)) = (M.op y (M.op X2 (M.op X3 X4))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e267 X0 X1 X2 X3 X4 x
               have i₂ := b5e192 X3 x (M.op X2 (M.op X3 X4))
               grind)
            | exact superpose b5e192 b5e267
            | exact resolve b5e267 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e267
          have b5e291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op y (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e261 X0 X1 X2 X3 x
               have i₂ := b5e192 X3 x (M.op X2 X3)
               grind)
            | exact superpose b5e192 b5e261
            | exact resolve b5e261 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e261
          have b5e304 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (M.op (M.op X1 X2) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e222 X0 X1 X2
               have i₂ := b5e13 (σ X0) (M.op X1 X2) (σ X0)
               grind)
            | exact superpose b5e13 b5e222
            | exact resolve b5e222 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e222
          have b5e318 : ∀ X2 X3 X4 : G, (M.op y (M.op X2 (M.op X3 X4))) = (M.op y (M.op X3 X4)) := by
            intro X2 X3 X4
            first
            | (have i₁ := b5e288 x x X2 X3 X4
               have i₂ := b5e192 (M.op x x) X2 (M.op X3 X4)
               grind)
            | exact superpose b5e192 b5e288
            | exact resolve b5e288 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e288
          have b5e320 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X2 X3)) = (M.op y (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e291 X0 X1 X2 X3
               have i₂ := b5e192 X2 X3 (M.op (M.op (M.op X0 X1) X2) X3)
               grind)
            | exact superpose b5e192 b5e291
            | exact resolve b5e291 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e291
          have b5e324 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op y (M.op X1 X2)) (σ X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e304 X0 X1 X2
               have i₂ := b5e42 (M.op X1 X2) (σ X0)
               grind)
            | exact superpose b5e42 b5e304
            | exact resolve b5e304 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e304
          have b5e329 : ∀ X2 X3 : G, (M.op y (M.op y X3)) = (M.op y (M.op X2 X3)) := by
            intro X2 X3
            first
            | (have i₁ := b5e320 x x X2 X3
               have i₂ := b5e192 (M.op x x) X2 X3
               grind)
            | exact superpose b5e192 b5e320
            | exact resolve b5e320 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e320
          have b5e330 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op y (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e324 X0 x x
               have i₂ := b5e192 y (M.op x x) (σ X0)
               grind)
            | exact superpose b5e192 b5e324
            | exact resolve b5e324 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e324
          have b5e625 : ∀ X0 X1 : G, (M.op y X1) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e192 (σ X0) (σ X0) X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e192
            | exact resolve b5e192 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e954 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e62 X0 X1
               have i₂ := b5e18 X0 (σ X1)
               grind)
            | exact superpose b5e18 b5e62
            | (have j1 := b5e18 X0 (σ X1)
               grind)
            | exact resolve b5e62 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e1010 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X2) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e32 (σ X0) X1 (σ X0) x
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e32
            | exact resolve b5e32 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1182 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op y (M.op (M.op (σ X0) X2) (σ X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1010 X0 X1 X2
               have i₂ := b5e625 X0 (M.op (M.op (σ X0) X2) (σ X0))
               grind)
            | exact superpose b5e625 b5e1010
            | exact resolve b5e1010 b5e625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1010
          have b5e1286 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op y (M.op y (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e1182 X0 X1 x
               have i₂ := b5e329 (M.op (σ X0) x) (σ X0)
               grind)
            | exact superpose b5e329 b5e1182
            | exact resolve b5e1182 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1182
          have b5e1380 : ∀ X0 : G, (M.op y (M.op y (σ X0))) = (M.op y (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e1286 X0 x
               have i₂ := b5e192 (σ X0) x (σ (M.op X0 X0))
               grind)
            | exact superpose b5e192 b5e1286
            | exact resolve b5e1286 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1286
          have b5e1474 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op (τ X0) (τ X0))
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e30
            | exact resolve b5e30 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1477 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e14 (M.op (τ X0) (τ X0))
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e14
            | exact resolve b5e14 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64
          have b5e1480 : ∀ X0 : G, (σ (M.op (M.op (τ X0) (τ X0)) (M.op (τ X0) (τ X0)))) = (M.op y (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e1474 X0
               have i₂ := b5e192 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e192 b5e1474
            | exact resolve b5e1474 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1474
          have b5e1482 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (σ (M.op y (M.op (τ X0) (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e1480 X0
               have i₂ := b5e192 (τ X0) (τ X0) (M.op (τ X0) (τ X0))
               grind)
            | exact superpose b5e192 b5e1480
            | exact resolve b5e1480 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1480
          have b5e1483 : ∀ X0 : G, (M.op y (M.op X0 X0)) = (σ (M.op y (M.op y (τ X0)))) := by
            intro X0
            first
            | (have i₁ := b5e1482 X0
               have i₂ := b5e329 (τ X0) (τ X0)
               grind)
            | exact superpose b5e329 b5e1482
            | exact resolve b5e1482 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1482
          have b5e1641 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have j0 := b5e48 X0 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e1642 : ∀ X0 : G, (M.op y X0) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1641 X0
               have i₂ := b5e284 X0 X0
               grind)
            | exact superpose b5e284 b5e1641
            | (have j0 := b5e1641 X0
               grind)
            | exact resolve b5e1641 b5e284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1641
          have b5e1690 : ∀ X0 : G, (k X0 (M.op y X0)) = X0 ∨ (M.op y X0) = X0 := by
            intro X0
            first
            | (have i₁ := b5e1642 X0
               have i₂ := b5e284 X0 X0
               grind)
            | exact superpose b5e284 b5e1642
            | (have j0 := b5e1642 X0
               grind)
            | exact resolve b5e1642 b5e284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1642
          have b5e1770 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 (σ X1) (σ X0)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e17
            | (have j0 := b5e17 (σ X0) (σ X1)
               have j1 := b5e53 X0 X1
               grind)
            | (have r₁ := b5e17 (σ X0) (σ X1)
               have r₂ := b5e53 X0 X1
               grind)
            | exact resolve b5e17 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1773 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 (σ X0)) (M.op (M.op X2 X3) (σ X0))) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e32 X2 X3 (σ X0) (σ X1)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e32
            | (have j1 := b5e53 X0 X1
               grind)
            | exact resolve b5e32 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e1786 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op y (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e284 (σ X1) (σ X0)
               have i₂ := b5e53 X0 X1
               grind)
            | exact superpose b5e53 b5e284
            | (have j1 := b5e53 X0 X1
               grind)
            | exact resolve b5e284 b5e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e1810 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b5e1770 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1770
          have b5e1838 : ∀ X0 X1 X2 X3 : G, (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) = (M.op y (M.op (M.op X2 X3) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e1773 X0 X1 X2 X3
               have i₂ := b5e192 X2 (σ X0) (M.op (M.op X2 X3) (σ X0))
               grind)
            | exact superpose b5e192 b5e1773
            | (have j0 := b5e1773 X0 X1 X2 X3
               grind)
            | exact resolve b5e1773 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1773
          have b5e1841 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1810 X0 X1
               have i₂ := b5e19 X1 X0
               grind)
            | exact superpose b5e19 b5e1810
            | (have j0 := b5e1810 X0 X1
               grind)
            | exact resolve b5e1810 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1810
          have b5e1856 : ∀ X0 X1 X2 : G, (M.op y (M.op y (σ X0))) = (M.op (σ (k X0 X1)) (M.op X2 (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1838 X0 X1 X2 x
               have i₂ := b5e329 (M.op X2 x) (σ X0)
               grind)
            | exact superpose b5e329 b5e1838
            | (have j0 := b5e1838 X0 X1 X2 x
               grind)
            | exact resolve b5e1838 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1838
          have b5e1893 : ∀ X0 : G, (M.op y (τ X0)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e284 (τ X0) (τ X0)
               have i₂ := b5e1477 X0
               grind)
            | exact superpose b5e1477 b5e284
            | exact resolve b5e284 b5e1477
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1477
          have b5e2209 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e30 (M.op X0 X0)
               have i₂ := b5e625 X0 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e625 b5e30
            | exact resolve b5e30 b5e625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2267 : ∀ X0 : G, (M.op y (σ (M.op X0 X0))) = (σ (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e2209 X0
               have i₂ := b5e192 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e192 b5e2209
            | exact resolve b5e2209 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2209
          have b5e2654 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e329 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e329
            | exact resolve b5e329 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2657 : ∀ X0 X1 X2 : G, (M.op y (M.op y (M.op y X0))) = (M.op y (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e329 X2 (M.op X1 X0)
               have i₂ := b5e329 X1 X0
               grind)
            | (have i₁ := b5e329 X2 (M.op y x)
               have i₂ := b5e329 X2 x
               grind)
            | exact superpose b5e329 b5e329
            | exact resolve b5e329 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2803 : ∀ X0 X1 X2 : G, (M.op y (M.op y X0)) = (M.op y (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e2657 X0 X1 X2
               have i₂ := b5e74 X0
               grind)
            | exact superpose b5e74 b5e2657
            | exact resolve b5e2657 b5e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e74 b5e2657
          have b5e3405 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (M.op y (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e111 X0 (σ (M.op X0 X0))
               have i₂ := b5e330 X0
               grind)
            | exact superpose b5e330 b5e111
            | exact resolve b5e111 b5e330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e111
          have b5e3609 : ∀ X0 : G, (M.op y (M.op y (σ X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e3405 X0
               have i₂ := b5e625 X0 (M.op y (σ X0))
               grind)
            | exact superpose b5e625 b5e3405
            | exact resolve b5e3405 b5e625
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e625 b5e3405
          have b5e3659 : ∀ X0 : G, (M.op y (M.op y (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e3609 X0
               have i₂ := b5e30 (M.op X0 X0)
               grind)
            | exact superpose b5e30 b5e3609
            | exact resolve b5e3609 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3609
          have b5e3680 : ∀ X0 : G, (M.op y (M.op y (σ X0))) = (σ (M.op y (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e3659 X0
               have i₂ := b5e192 X0 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e192 b5e3659
            | exact resolve b5e3659 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3659
          have b5e6803 : ∀ X0 : G, (σ (M.op y (M.op y X0))) = (M.op y (M.op (σ X0) (σ X0))) := by
            intro X0
            first
            | (have i₁ := b5e1483 (σ X0)
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e1483
            | exact resolve b5e1483 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1483
          have b5e6911 : ∀ X0 : G, (M.op y (M.op y (σ X0))) = (σ (M.op y (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e6803 X0
               have i₂ := b5e329 (σ X0) (σ X0)
               grind)
            | exact superpose b5e329 b5e6803
            | exact resolve b5e6803 b5e329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e329 b5e6803
          have b5e8379 : ∀ X0 X1 : G, (σ (M.op y (M.op y X0))) = (M.op y (M.op y (σ (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3680 (M.op X1 X0)
               have i₂ := b5e2803 X0 X1 (M.op X1 X0)
               grind)
            | exact superpose b5e2803 b5e3680
            | exact resolve b5e3680 b5e2803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2803 b5e3680
          have b5e8507 : ∀ X0 X1 : G, (σ (M.op y (M.op y X0))) = (σ (M.op y (M.op y (M.op X1 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e8379 X0 X1
               have i₂ := b5e6911 (M.op X1 X0)
               grind)
            | exact superpose b5e6911 b5e8379
            | exact resolve b5e8379 b5e6911
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e6911 b5e8379
          have b5e8544 : ∀ X0 X1 : G, (σ (M.op y (M.op y X0))) = (σ (M.op y (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e8507 X0 X1
               have i₂ := b5e318 y X1 X0
               grind)
            | (have i₁ := b5e8507 X0 X1
               have i₂ := b5e318 x y (M.op X1 X0)
               grind)
            | exact superpose b5e318 b5e8507
            | exact resolve b5e8507 b5e318
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e318 b5e8507
          have b5e13291 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e59 (σ X0) X1
               have i₂ := b5e14 X0
               grind)
            | exact superpose b5e14 b5e59
            | exact resolve b5e59 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e13355 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13291 X0 X1
               have i₂ := b5e19 X0 X1
               grind)
            | exact superpose b5e19 b5e13291
            | (have j0 := b5e13291 X0 X1
               grind)
            | exact resolve b5e13291 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13291
          have b5e19560 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e1841 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e1841
            | (have j0 := b5e1841 x y
               grind)
            | exact resolve b5e1841 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1841
          have b5e19563 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
          clear b5e19560
          have b5e19567 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e19563
               have r₂ := b5e23
               grind)
            | exact resolve b5e19563 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19563
          have b5e19576 : (σ y) = (σ (k y x)) := by
            first
            | (have r₁ := b5e19567
               have r₂ := b5e24
               grind)
            | exact resolve b5e19567 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19567
          have b5e19590 : (k y x) = (τ (σ y)) := by
            first
            | (have i₁ := b5e14 (k y x)
               have i₂ := b5e19576
               grind)
            | exact superpose b5e19576 b5e14
            | exact resolve b5e14 b5e19576
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19576
          have b5e19645 : y = (k y x) := by
            first
            | (have i₁ := b5e19590
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e19590
            | exact resolve b5e19590 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19590
          have b5e20806 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1856 x y X0
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e1856
            | (have j0 := b5e1856 x y x
               grind)
            | exact resolve b5e1856 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1856
          have b5e21007 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e20806 X0
               grind)
            | (have r₁ := b5e20806 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e20806 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e20806
          have b5e21060 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (σ x) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have j0 := b5e21007 X0
               grind)
            | (have r₁ := b5e21007 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e21007 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21007
          have b5e21094 : ∀ X0 : G, (M.op y (M.op y (σ x))) = (M.op (M.op y X0) (σ x)) := by
            intro X0
            first
            | (have i₁ := b5e21060 X0
               have i₂ := b5e42 X0 (σ x)
               grind)
            | exact superpose b5e42 b5e21060
            | exact resolve b5e21060 b5e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42 b5e21060
          have b5e21109 : (M.op y (σ x)) = (M.op y (M.op y (σ x))) := by
            first
            | (have i₁ := b5e21094 x
               have i₂ := b5e192 y x (σ x)
               grind)
            | exact superpose b5e192 b5e21094
            | exact resolve b5e21094 b5e192
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21094
          have b5e21119 : (M.op y (σ x)) = (M.op y (σ (M.op x x))) := by
            first
            | (have i₁ := b5e21109
               have i₂ := b5e1380 x
               grind)
            | exact superpose b5e1380 b5e21109
            | exact resolve b5e21109 b5e1380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1380 b5e21109
          have b5e21128 : (σ (M.op y (M.op x x))) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e21119
               have i₂ := b5e2267 x
               grind)
            | exact superpose b5e2267 b5e21119
            | exact resolve b5e21119 b5e2267
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2267 b5e21119
          have b5e21132 : (σ (M.op y (M.op y x))) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e21128
               have i₂ := b5e8544 x x
               grind)
            | exact superpose b5e8544 b5e21128
            | exact resolve b5e21128 b5e8544
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e8544 b5e21128
          have b5e21134 : (σ (M.op y y)) = (M.op y (σ x)) := by
            first
            | (have i₁ := b5e21132
               have i₂ := b5e2654 y
               grind)
            | exact superpose b5e2654 b5e21132
            | exact resolve b5e21132 b5e2654
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2654 b5e21132
          have b5e21155 : (σ x) = (k (σ x) (σ (M.op y y))) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e1690 (σ x)
               have i₂ := b5e21134
               grind)
            | exact superpose b5e21134 b5e1690
            | exact resolve b5e1690 b5e21134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1690
          have b5e21191 : (σ (M.op y y)) = (M.op (σ x) (σ (M.op y y))) := by
            first
            | (have i₁ := b5e284 (σ x) y
               have i₂ := b5e21134
               grind)
            | exact superpose b5e21134 b5e284
            | exact resolve b5e284 b5e21134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e284
          have b5e21234 : (σ x) = (σ (k x (M.op y y))) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e21155
               have i₂ := b5e19 x (M.op y y)
               grind)
            | exact superpose b5e19 b5e21155
            | exact resolve b5e21155 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21155
          have b5e75144 : (M.op (σ y) (σ x)) = (M.op y (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e1786 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e1786
            | (have j0 := b5e1786 x y
               grind)
            | exact resolve b5e1786 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e1786
          have b5e75407 : (M.op (σ y) (σ x)) = (M.op y (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b5e75144
               have r₂ := b5e24
               grind)
            | exact resolve b5e75144 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75144
          have b5e75519 : (M.op (σ y) (σ x)) = (M.op y (σ y)) := by
            first
            | (have r₁ := b5e75407
               have r₂ := b5e23
               grind)
            | exact resolve b5e75407 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75407
          have b5e75709 : (σ y) ≠ (M.op y (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e75519
               grind)
            | exact superpose b5e75519 b5e24
            | exact resolve b5e24 b5e75519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75720 : (τ (M.op y (σ y))) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e954 (σ y) x
               have i₂ := b5e75519
               grind)
            | exact superpose b5e75519 b5e954
            | (have j0 := b5e954 (σ y) x
               grind)
            | exact resolve b5e954 b5e75519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e954 b5e75519
          have b5e75847 : (τ (M.op y (σ y))) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e75720
               have r₂ := b5e23
               grind)
            | exact resolve b5e75720 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75720
          have b5e75888 : (k y x) = (τ (M.op y (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e75847
               have i₂ := b5e14 y
               grind)
            | exact superpose b5e14 b5e75847
            | exact resolve b5e75847 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75847
          have b5e75924 : y = (τ (M.op y (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e75888
               have i₂ := b5e19645
               grind)
            | exact superpose b5e19645 b5e75888
            | exact resolve b5e75888 b5e19645
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e19645 b5e75888
          have b5e77854 : (σ y) = (M.op y (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e15 (M.op y (σ y))
               have i₂ := b5e75924
               grind)
            | exact superpose b5e75924 b5e15
            | exact resolve b5e15 b5e75924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75924
          have b5e77920 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e77854
               have r₂ := b5e75709
               grind)
            | exact resolve b5e77854 b5e75709
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e77854
          have b5e78094 : (M.op (σ x) (σ (M.op x x))) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e112 x (σ y)
               have i₂ := b5e77920
               grind)
            | exact superpose b5e77920 b5e112
            | exact resolve b5e112 b5e77920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
          have b5e78135 : ∀ X0 : G, (M.op y X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e192 (σ x) (σ y) X0
               have i₂ := b5e77920
               grind)
            | exact superpose b5e77920 b5e192
            | exact resolve b5e192 b5e77920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e192 b5e77920
          have b5e78247 : (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b5e78094
               have i₂ := b5e30 x
               grind)
            | exact superpose b5e30 b5e78094
            | exact resolve b5e78094 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e78094
          have b5e78299 : (M.op y (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e78247
               have i₂ := b5e330 x
               grind)
            | exact superpose b5e330 b5e78247
            | exact resolve b5e78247 b5e330
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e330 b5e78247
          have b5e78336 : (σ (M.op y y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e78299
               have i₂ := b5e21134
               grind)
            | exact superpose b5e21134 b5e78299
            | exact resolve b5e78299 b5e21134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78299
          have b5e78911 : (M.op y (τ (σ x))) = (M.op (τ (σ x)) (τ (M.op y (σ x)))) := by
            first
            | (have i₁ := b5e1893 (σ x)
               have i₂ := b5e78135 (σ x)
               grind)
            | exact superpose b5e78135 b5e1893
            | exact resolve b5e1893 b5e78135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1893
          have b5e79157 : (M.op y (τ (σ x))) = (M.op (τ (σ x)) (τ (σ (M.op y y)))) := by
            first
            | (have i₁ := b5e78911
               have i₂ := b5e21134
               grind)
            | exact superpose b5e21134 b5e78911
            | exact resolve b5e78911 b5e21134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21134 b5e78911
          have b5e79251 : (M.op y (τ (σ x))) = (M.op (τ (σ x)) (M.op y y)) := by
            first
            | (have i₁ := b5e79157
               have i₂ := b5e14 (M.op y y)
               grind)
            | exact superpose b5e14 b5e79157
            | exact resolve b5e79157 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79157
          have b5e79316 : (M.op y x) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e79251
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e79251
            | exact resolve b5e79251 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79251
          have b5e79367 : y = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b5e79316
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e79316
            | exact resolve b5e79316 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79316
          have b5e81212 : (M.op x x) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b5e14 (M.op x x)
               have i₂ := b5e78336
               grind)
            | exact superpose b5e78336 b5e14
            | exact resolve b5e14 b5e78336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78336
          have b5e81369 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b5e81212
               have i₂ := b5e14 (M.op y y)
               grind)
            | exact superpose b5e14 b5e81212
            | exact resolve b5e81212 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81212
          have b5e125730 : (σ x) = (σ (M.op x (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e13355 x (M.op y y)
               have i₂ := b5e21234
               grind)
            | exact superpose b5e21234 b5e13355
            | (have j0 := b5e13355 x (M.op y y)
               grind)
            | exact resolve b5e13355 b5e21234
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e13355 b5e21234
          have b5e125833 : (σ x) = (σ y) ∨ (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e125730
               have i₂ := b5e79367
               grind)
            | exact superpose b5e79367 b5e125730
            | exact resolve b5e125730 b5e79367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125730
          have b5e125848 : (M.op y y) = (M.op (M.op y y) x) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e125833
               have r₂ := b5e23
               grind)
            | exact resolve b5e125833 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125833
          have b5e125863 : (M.op x (M.op y x)) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e125848
               have i₂ := b5e13 x y y
               grind)
            | exact superpose b5e13 b5e125848
            | exact resolve b5e125848 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125848
          have b5e125876 : (M.op y x) = (M.op y y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e125863
               have i₂ := b5e35 x
               grind)
            | exact superpose b5e35 b5e125863
            | exact resolve b5e125863 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e125863
          have b5e125884 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e125876
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e125876
            | exact resolve b5e125876 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125876
          have b5e167538 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e125884
               grind)
            | exact superpose b5e125884 b5e14
            | exact resolve b5e14 b5e125884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e125884
          have b5e167594 : x = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e167538
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e167538
            | exact resolve b5e167538 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e167538
          have b5e167595 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b5e167594
          have b5e167852 : y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e79367
               have i₂ := b5e167595
               grind)
            | exact superpose b5e167595 b5e79367
            | exact resolve b5e79367 b5e167595
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79367 b5e167595
          have b5e168158 : y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b5e167852
               have i₂ := b5e81369
               grind)
            | exact superpose b5e81369 b5e167852
            | exact resolve b5e167852 b5e81369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81369 b5e167852
          have b5e168159 : y = (M.op y y) := by grind
          clear b5e168158
          have b5e168290 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e21191
               have i₂ := b5e168159
               grind)
            | exact superpose b5e168159 b5e21191
            | exact resolve b5e21191 b5e168159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e21191 b5e168159
          have b5e168541 : (σ y) = (M.op y (σ y)) := by
            first
            | (have i₁ := b5e168290
               have i₂ := b5e78135 (σ y)
               grind)
            | exact superpose b5e78135 b5e168290
            | exact resolve b5e168290 b5e78135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78135 b5e168290
          have b5e168557 : False := by grind
          exact b5e168557
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X0) := by
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
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e19 X1 (τ X0)
               have i₂ := b7e15 X0
               grind)
            | exact superpose b7e15 b7e19
            | exact resolve b7e19 b7e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e32 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ x)) := by
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
          have b7e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op X1 X2) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X0 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X3 X2 (M.op X0 X2)
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e46 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e48 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X2) = X0 ∨ (k X0 (M.op X1 X2)) = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e17 X0 (M.op X1 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e17
            | (have j0 := b7e17 (M.op X1 X2) X0
               grind)
            | (have r₁ := b7e17 X0 (M.op X0 (M.op X0 X0))
               have r₂ := b7e13 X0 X0 (M.op X0 X0)
               grind)
            | exact resolve b7e17 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e49 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e46
          have b7e50 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e49
               have r₂ := b7e23
               grind)
            | exact resolve b7e49 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e49
          have b7e51 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e50
            | exact resolve b7e50 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e54 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e14
            | exact resolve b7e14 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e55 : x = (k x y) := by
            first
            | (have i₁ := b7e54
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e54
            | exact resolve b7e54 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e60 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e26 X0 X1
               have i₂ := b7e18 (τ X0) X1
               grind)
            | exact superpose b7e18 b7e26
            | (have j1 := b7e18 (τ X0) X1
               grind)
            | exact resolve b7e26 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e61 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e51
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e51
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e51 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : (σ (M.op x y)) = (σ x) ∨ x = y := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e22
               grind)
            | exact resolve b7e61 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e63 : (σ (M.op x y)) = (σ x) := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e21
               grind)
            | exact resolve b7e62 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e65 : x = (M.op x y) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e55
               grind)
            | exact superpose b7e55 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e66 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e22
               grind)
            | exact resolve b7e65 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e68 : x = (M.op x y) := by
            first
            | (have r₁ := b7e66
               have r₂ := b7e21
               grind)
            | exact resolve b7e66 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e77 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e14 (k X0 (τ X1))
               have i₂ := b7e27 X1 X0
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e83 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e13
            | exact resolve b7e13 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e110 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 (σ y) X0 X1 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e35
            | exact resolve b7e35 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e111 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 (σ X0) X1 X2 (σ X0)
               have i₂ := b7e30 X0
               grind)
            | exact superpose b7e30 b7e35
            | exact resolve b7e35 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e127 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op y y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e110 x X1
               have i₂ := b7e111 y x X1
               grind)
            | exact superpose b7e111 b7e110
            | exact resolve b7e110 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e110
          have b7e138 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b7e36 (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e139 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op y y))) := by
            first
            | (have i₁ := b7e36 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e36
            | exact resolve b7e36 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e147 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e35 X0 (M.op (σ y) X0) X1 X2
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e35
            | exact resolve b7e35 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35
          have b7e149 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0 (M.op (σ y) X0)
               have i₂ := b7e36 X0
               grind)
            | exact superpose b7e36 b7e13
            | exact resolve b7e13 b7e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e154 : ∀ X0 X1 : G, (M.op (σ (M.op y y)) X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e149 X0 X1
               have i₂ := b7e111 y X0 X1
               grind)
            | exact superpose b7e111 b7e149
            | exact resolve b7e149 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e155 : ∀ X0 X1 X2 : G, (M.op (σ (M.op y y)) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e147 X0 X1 X2
               have i₂ := b7e111 y X0 X1
               grind)
            | exact superpose b7e111 b7e147
            | exact resolve b7e147 b7e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e111 b7e147
          have b7e161 : ∀ X0 X1 : G, (M.op (σ y) X1) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e154 X0 X1
               have i₂ := b7e127 X1
               grind)
            | exact superpose b7e127 b7e154
            | exact resolve b7e154 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154
          have b7e162 : ∀ X0 X1 X2 : G, (M.op (σ y) X1) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e155 X0 X1 X2
               have i₂ := b7e127 X1
               grind)
            | exact superpose b7e127 b7e155
            | exact resolve b7e155 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e155
          have b7e218 : (M.op (σ x) (σ y)) = (M.op (M.op x (σ y)) (σ x)) := by
            first
            | (have i₁ := b7e32 (M.op x (σ y))
               have i₂ := b7e83 (σ y)
               grind)
            | exact superpose b7e83 b7e32
            | exact resolve b7e32 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e221 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x (σ x))) := by
            first
            | (have i₁ := b7e218
               have i₂ := b7e13 (σ x) x (σ y)
               grind)
            | exact superpose b7e13 b7e218
            | exact resolve b7e218 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e218
          have b7e232 : (M.op (σ x) (σ y)) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e221
               have i₂ := b7e83 (σ x)
               grind)
            | exact superpose b7e83 b7e221
            | exact resolve b7e221 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e221
          have b7e233 : (σ y) = (M.op x (σ x)) := by
            first
            | (have i₁ := b7e232
               have i₂ := b7e138
               grind)
            | exact superpose b7e138 b7e232
            | exact resolve b7e232 b7e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138 b7e232
          have b7e276 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) x) X2) = (M.op x X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e83 X2
               have i₂ := b7e37 X0 X1 x X2
               grind)
            | exact superpose b7e37 b7e83
            | exact resolve b7e83 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e277 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (M.op X3 X4) (M.op X2 X3)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b7e13 (M.op X2 X3) X3 X4
               have i₂ := b7e37 X0 X1 X2 X3
               grind)
            | exact superpose b7e37 b7e13
            | exact resolve b7e13 b7e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e37
          have b7e303 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op (M.op (M.op X0 X1) X2) X3)) = (M.op (σ y) (M.op X2 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e277 X0 X1 X2 X3 x
               have i₂ := b7e162 X3 (M.op X2 X3) x
               grind)
            | exact superpose b7e162 b7e277
            | exact resolve b7e277 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e277
          have b7e304 : ∀ X2 : G, (M.op (σ y) X2) = (M.op x X2) := by
            intro X2
            first
            | (have i₁ := b7e276 x x X2
               have i₂ := b7e162 (M.op x x) X2 x
               grind)
            | exact superpose b7e162 b7e276
            | exact resolve b7e276 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e276
          have b7e332 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op (σ y) (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e303 X0 X1 X2 X3
               have i₂ := b7e162 X2 (M.op (M.op (M.op X0 X1) X2) X3) X3
               grind)
            | exact superpose b7e162 b7e303
            | exact resolve b7e303 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e303
          have b7e343 : ∀ X0 X1 X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op x (M.op (M.op (M.op X0 X1) X2) X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e332 X0 X1 X2 X3
               have i₂ := b7e304 (M.op (M.op (M.op X0 X1) X2) X3)
               grind)
            | exact superpose b7e304 b7e332
            | exact resolve b7e332 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e332
          have b7e352 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op x (M.op (σ y) X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e343 x x X2 X3
               have i₂ := b7e162 (M.op x x) X3 X2
               grind)
            | exact superpose b7e162 b7e343
            | exact resolve b7e343 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e343
          have b7e358 : ∀ X2 X3 : G, (M.op (σ y) (M.op X2 X3)) = (M.op x (M.op x X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e352 X2 X3
               have i₂ := b7e304 X3
               grind)
            | exact superpose b7e304 b7e352
            | exact resolve b7e352 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e352
          have b7e362 : ∀ X2 X3 : G, (M.op x (M.op x X3)) = (M.op x (M.op X2 X3)) := by
            intro X2 X3
            first
            | (have i₁ := b7e358 X2 X3
               have i₂ := b7e304 (M.op X2 X3)
               grind)
            | exact superpose b7e304 b7e358
            | exact resolve b7e358 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e358
          have b7e943 : (σ (M.op y y)) = (M.op x (σ y)) := by
            first
            | (have i₁ := b7e30 y
               have i₂ := b7e304 (σ y)
               grind)
            | exact superpose b7e304 b7e30
            | exact resolve b7e30 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1857 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (σ y)) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e34 (σ y) x X0 X1
               have i₂ := b7e943
               grind)
            | exact superpose b7e943 b7e34
            | exact resolve b7e34 b7e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e1872 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (σ y)) = (M.op x (M.op (σ y) (σ (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1857 X0 X1
               have i₂ := b7e304 (M.op (σ y) (σ (M.op y y)))
               grind)
            | exact superpose b7e304 b7e1857
            | exact resolve b7e1857 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1857
          have b7e1878 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (σ y)) = (M.op x (M.op x (σ (M.op y y)))) := by
            intro X0 X1
            first
            | (have i₁ := b7e1872 X0 X1
               have i₂ := b7e362 (σ y) (σ (M.op y y))
               grind)
            | exact superpose b7e362 b7e1872
            | exact resolve b7e1872 b7e362
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e362 b7e1872
          have b7e1882 : (M.op (σ y) (σ y)) = (M.op x (M.op x (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e1878 x x
               have i₂ := b7e162 (M.op x x) (σ y) x
               grind)
            | exact superpose b7e162 b7e1878
            | exact resolve b7e1878 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1878
          have b7e1885 : (M.op x (σ y)) = (M.op x (M.op x (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e1882
               have i₂ := b7e304 (σ y)
               grind)
            | exact superpose b7e304 b7e1882
            | exact resolve b7e1882 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1882
          have b7e1887 : (σ (M.op y y)) = (M.op x (M.op x (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e1885
               have i₂ := b7e943
               grind)
            | exact superpose b7e943 b7e1885
            | exact resolve b7e1885 b7e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1885
          have b7e1938 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have j0 := b7e48 X0 X0 (M.op X0 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e1939 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1938 X0
               have i₂ := b7e161 X0 X0
               grind)
            | exact superpose b7e161 b7e1938
            | (have j0 := b7e1938 X0
               grind)
            | exact resolve b7e1938 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1938
          have b7e1987 : ∀ X0 : G, (M.op x X0) = X0 ∨ (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1939 X0
               have i₂ := b7e304 X0
               grind)
            | exact superpose b7e304 b7e1939
            | (have j0 := b7e1939 X0
               grind)
            | exact resolve b7e1939 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1939
          have b7e2030 : ∀ X0 : G, (k X0 (M.op (σ y) X0)) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e1987 X0
               have i₂ := b7e161 X0 X0
               grind)
            | exact superpose b7e161 b7e1987
            | (have j0 := b7e1987 X0
               grind)
            | exact resolve b7e1987 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1987
          have b7e2062 : ∀ X0 : G, (k X0 (M.op x X0)) = X0 ∨ (M.op x X0) = X0 := by
            intro X0
            first
            | (have i₁ := b7e2030 X0
               have i₂ := b7e304 X0
               grind)
            | exact superpose b7e304 b7e2030
            | (have j0 := b7e2030 X0
               grind)
            | exact resolve b7e2030 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2030
          have b7e2849 : (M.op (σ y) (σ (M.op y y))) = (σ (M.op (M.op y y) (M.op y y))) := by
            first
            | (have i₁ := b7e30 (M.op y y)
               have i₂ := b7e127 (σ (M.op y y))
               grind)
            | exact superpose b7e127 b7e30
            | exact resolve b7e30 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e2879 : (M.op x (σ (M.op y y))) = (M.op (σ y) (M.op x (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e83 (σ (M.op y y))
               have i₂ := b7e127 (M.op x (σ (M.op y y)))
               grind)
            | exact superpose b7e127 b7e83
            | exact resolve b7e83 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e127
          have b7e2882 : (M.op x (σ (M.op y y))) = (M.op x (M.op x (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e2879
               have i₂ := b7e304 (M.op x (σ (M.op y y)))
               grind)
            | exact superpose b7e304 b7e2879
            | exact resolve b7e2879 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2879
          have b7e2909 : (M.op (σ y) (σ (M.op y y))) = (σ (M.op (σ y) (M.op y y))) := by
            first
            | (have i₁ := b7e2849
               have i₂ := b7e162 y (M.op y y) y
               grind)
            | exact superpose b7e162 b7e2849
            | exact resolve b7e2849 b7e162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e162 b7e2849
          have b7e2921 : (σ (M.op y y)) = (M.op x (σ (M.op y y))) := by
            first
            | (have i₁ := b7e2882
               have i₂ := b7e1887
               grind)
            | exact superpose b7e1887 b7e2882
            | exact resolve b7e2882 b7e1887
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1887 b7e2882
          have b7e2935 : (M.op (σ y) (σ (M.op y y))) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b7e2909
               have i₂ := b7e304 (M.op y y)
               grind)
            | exact superpose b7e304 b7e2909
            | exact resolve b7e2909 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2909
          have b7e2954 : (σ (M.op y y)) = (σ (M.op x (M.op y y))) := by
            first
            | (have i₁ := b7e2935
               have i₂ := b7e139
               grind)
            | exact superpose b7e139 b7e2935
            | exact resolve b7e2935 b7e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139 b7e2935
          have b7e4081 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op x (σ X0)))) ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e77 X0 (M.op x (σ X0))
               have i₂ := b7e2062 (σ X0)
               grind)
            | exact superpose b7e2062 b7e77
            | (have j1 := b7e2062 (σ X0)
               grind)
            | exact resolve b7e77 b7e2062
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e2062
          have b7e4086 : ∀ X0 : G, (k X0 (τ (M.op x (σ X0)))) = X0 ∨ (σ X0) = (M.op x (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e4081 X0
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e4081
            | (have j0 := b7e4081 X0
               grind)
            | exact resolve b7e4081 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4081
          have b7e17458 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e60 (σ X0) X1
               have i₂ := b7e14 X0
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e17521 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e17458 X0 X1
               have i₂ := b7e19 X0 X1
               grind)
            | exact superpose b7e19 b7e17458
            | (have j0 := b7e17458 X0 X1
               grind)
            | exact resolve b7e17458 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e17458
          have b7e59384 : y = (k y (τ (σ (M.op y y)))) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e4086 y
               have i₂ := b7e943
               grind)
            | exact superpose b7e943 b7e4086
            | exact resolve b7e4086 b7e943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e943 b7e4086
          have b7e59444 : y = (k y (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e59384
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e59384
            | exact resolve b7e59384 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59384
          have b7e67783 : (σ y) = (σ (M.op y (M.op y y))) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e17521 y (M.op y y)
               have i₂ := b7e59444
               grind)
            | exact superpose b7e59444 b7e17521
            | (have j0 := b7e17521 y (M.op y y)
               grind)
            | exact resolve b7e17521 b7e59444
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e17521 b7e59444
          have b7e67801 : (σ y) = (σ (M.op (σ y) y)) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67783
               have i₂ := b7e161 y y
               grind)
            | exact superpose b7e161 b7e67783
            | exact resolve b7e67783 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67783
          have b7e67810 : (σ (M.op x y)) = (σ y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67801
               have i₂ := b7e304 y
               grind)
            | exact superpose b7e304 b7e67801
            | exact resolve b7e67801 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67801
          have b7e67818 : (σ x) = (σ y) ∨ (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67810
               have i₂ := b7e63
               grind)
            | exact superpose b7e63 b7e67810
            | exact resolve b7e67810 b7e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e63 b7e67810
          have b7e67823 : (M.op y y) = (M.op (M.op y y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b7e67818
               have r₂ := b7e23
               grind)
            | exact resolve b7e67818 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67818
          have b7e67826 : (M.op y y) = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67823
               have i₂ := b7e13 y y y
               grind)
            | exact superpose b7e13 b7e67823
            | exact resolve b7e67823 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67823
          have b7e67829 : (M.op y y) = (M.op (σ y) y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67826
               have i₂ := b7e161 y y
               grind)
            | exact superpose b7e161 b7e67826
            | exact resolve b7e67826 b7e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e161 b7e67826
          have b7e67832 : (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67829
               have i₂ := b7e304 y
               grind)
            | exact superpose b7e304 b7e67829
            | exact resolve b7e67829 b7e304
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e304 b7e67829
          have b7e67835 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e67832
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e67832
            | exact resolve b7e67832 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67832
          have b7e237913 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e67835
               grind)
            | exact superpose b7e67835 b7e14
            | exact resolve b7e14 b7e67835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67835
          have b7e237932 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b7e237913
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e237913
            | exact resolve b7e237913 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e237913
          have b7e237933 : x = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b7e237932
          have b7e238310 : (σ x) = (M.op x (σ x)) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e2921
               have i₂ := b7e237933
               grind)
            | exact superpose b7e237933 b7e2921
            | exact resolve b7e2921 b7e237933
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2921 b7e237933
          have b7e238643 : (σ x) = (σ y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e238310
               have i₂ := b7e233
               grind)
            | exact superpose b7e233 b7e238310
            | exact resolve b7e238310 b7e233
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e233 b7e238310
          have b7e238693 : y = (M.op y y) := by
            first
            | (have r₁ := b7e238643
               have r₂ := b7e23
               grind)
            | exact resolve b7e238643 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e238643
          have b7e239041 : (σ (M.op x y)) = (σ y) := by
            first
            | (have i₁ := b7e2954
               have i₂ := b7e238693
               grind)
            | exact superpose b7e238693 b7e2954
            | exact resolve b7e2954 b7e238693
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2954 b7e238693
          have b7e239508 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e239041
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e239041
            | exact resolve b7e239041 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e239041
          have b7e239668 : False := by grind
          exact b7e239668
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e59 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e769 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e59 x y
               grind)
            | exact superpose b8e59 b8e20
            | (have j1 := b8e59 x y
               grind)
            | exact resolve b8e20 b8e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e59
          have b8e822 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e769
               have r₂ := b8e24
               grind)
            | exact resolve b8e769 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e769
          have b8e831 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e822
               have r₂ := b8e23
               grind)
            | exact resolve b8e822 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e822
          have b8e836 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b8e831
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e831
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e831
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e831
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e831 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e831
          have b8e837 : y = (M.op y x) ∨ x = y := by grind
          clear b8e836
          have b8e838 : x = y := by
            first
            | (have r₁ := b8e837
               have r₂ := b8e22
               grind)
            | exact resolve b8e837 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e837
          have b8e839 : False := by grind
          exact b8e839

/-- `Equation4449`: `x ◇ (y ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4449 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4449 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 (M.op X0 X2) X2 X3
           have i₂ := b0e11 X2 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 (M.op X1 X2) X3
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) X0) (σ x)) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e11 x X0 X3
           have i₂ := b0e11 x X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op X0 X3)
           have i₂ := b0e11 X3 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X1 x
           have i₂ := b0e11 X2 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (M.op x y) = (M.op y x) := by
        first
        | (have i₁ := b0e40 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e40
        | exact resolve b0e40 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X1 : G, (M.op y x) = (M.op (M.op x X1) x) := by
        intro X1
        first
        | (have i₁ := b0e11 x x X1
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x X0) (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op x X0) X0 X1
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e11
        | exact resolve b0e11 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
      have b0e121 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op x X0)) = (M.op (M.op y x) (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 (M.op x X0) X1 x
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e36
        | exact resolve b0e36 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e140 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op x X0)) = (M.op (M.op x y) (M.op x X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e121 X0 X1
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e121
        | exact resolve b0e121 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e121
      have b0e151 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op x X0)) (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e140 X0 x
           have i₂ := b0e47 (M.op x X0) x
           grind)
        | exact superpose b0e47 b0e140
        | exact resolve b0e140 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e140
      have b0e156 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x (M.op x X0)) (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e151 X0
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e151
        | exact resolve b0e151 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e151
      have b0e198 : ∀ X0 X1 : G, (M.op x (M.op y x)) = (M.op X0 (M.op (M.op x X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0 (M.op x X1) x
           have i₂ := b0e45 X1
           grind)
        | exact superpose b0e45 b0e41
        | exact resolve b0e41 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e200 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e41 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e41
        | exact resolve b0e41 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e201 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op x (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e41 X0 y x
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e41
        | exact resolve b0e41 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e226 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x X1) X0)) = (M.op x (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e198 X0 X1
           have i₂ := b0e201 x
           grind)
        | exact superpose b0e201 b0e198
        | exact resolve b0e198 b0e201
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e198 b0e201
      have b0e371 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op X1 X2) X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e37 X1 X2 (M.op x X0) X0
           have i₂ := b0e200 X0
           grind)
        | exact superpose b0e200 b0e37
        | exact resolve b0e37 b0e200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e455 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op X0 (M.op (M.op x (M.op (M.op X1 X2) X1)) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e200 (M.op (M.op X1 X2) X1)
           have i₂ := b0e37 X1 X2 X0 (M.op x (M.op (M.op X1 X2) X1))
           grind)
        | exact superpose b0e37 b0e200
        | exact resolve b0e200 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e460 : (M.op x y) = (M.op x (M.op x y)) := by
        first
        | (have i₁ := b0e455 x x x
           have i₂ := b0e226 x (M.op (M.op x x) x)
           grind)
        | exact superpose b0e226 b0e455
        | exact resolve b0e455 b0e226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e455
      have b0e514 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X3 X2) (M.op (M.op X3 X4) X3)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e33 X3 X4 X2 (M.op X1 X2)
           have i₂ := b0e41 X2 X1 X0
           grind)
        | (have i₁ := b0e33 X3 X4 X2 (M.op X1 X2)
           have i₂ := b0e41 X0 X1 X2
           grind)
        | exact superpose b0e41 b0e33
        | exact resolve b0e33 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e516 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X1 X2 X0 (M.op x X0)
           have i₂ := b0e200 X0
           grind)
        | exact superpose b0e200 b0e33
        | exact resolve b0e33 b0e200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e542 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) X1) (M.op x X0)) = (M.op (M.op x y) (M.op (M.op X0 X2) X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e33 X0 X2 (M.op x X0) X1
           have i₂ := b0e200 X0
           grind)
        | exact superpose b0e200 b0e33
        | exact resolve b0e33 b0e200
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e200
      have b0e600 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X4) (M.op X1 X3)) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X1 (M.op X1 X3) X4
           have i₂ := b0e33 X0 X2 X1 X3
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e608 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op (M.op (M.op X0 X3) X4) (M.op X0 X3)) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e37 X0 X3 X2 (M.op (M.op (M.op X0 X3) X4) (M.op X0 X3))
           have i₂ := b0e33 (M.op X0 X3) X4 X0 X1
           grind)
        | exact superpose b0e33 b0e37
        | exact resolve b0e37 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e618 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op x X2) (M.op x y))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e608 X0 X1 X2 x x
           have i₂ := b0e371 X2 (M.op X0 x) x
           grind)
        | exact superpose b0e371 b0e608
        | exact resolve b0e608 b0e371
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e371 b0e608
      have b0e621 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) = (M.op (M.op x (M.op X1 X3)) (M.op y x)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e600 X0 X1 X2 X3 x
           have i₂ := b0e47 (M.op X1 X3) x
           grind)
        | exact superpose b0e47 b0e600
        | exact resolve b0e600 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e600
      have b0e643 : ∀ X0 X2 : G, (M.op (M.op x (M.op x X0)) (M.op y x)) = (M.op (M.op x y) (M.op (M.op X0 X2) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e542 X0 x X2
           have i₂ := b0e47 (M.op x X0) x
           grind)
        | exact superpose b0e47 b0e542
        | exact resolve b0e542 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e542
      have b0e652 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op x y) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e514 X0 X1 X2 x x
           have i₂ := b0e516 X2 x x
           grind)
        | exact superpose b0e516 b0e514
        | exact resolve b0e514 b0e516
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e514
      have b0e658 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) = (M.op (M.op x (M.op X1 X3)) (M.op x y)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e621 X0 X1 X2 X3
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e621
        | exact resolve b0e621 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e621
      have b0e673 : ∀ X0 X2 : G, (M.op (M.op x (M.op x X0)) (M.op x y)) = (M.op (M.op x y) (M.op (M.op X0 X2) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e643 X0 X2
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e643
        | exact resolve b0e643 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e643
      have b0e681 : ∀ X1 X3 : G, (M.op (M.op x (M.op X1 X3)) (M.op x y)) = (M.op X1 (M.op (M.op x y) X1)) := by
        intro X1 X3
        first
        | (have i₁ := b0e658 x X1 x X3
           have i₂ := b0e516 X1 x x
           grind)
        | exact superpose b0e516 b0e658
        | exact resolve b0e658 b0e516
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e516 b0e658
      have b0e692 : ∀ X0 X2 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x y) (M.op (M.op X0 X2) X0)) := by
        intro X0 X2
        first
        | (have i₁ := b0e673 X0 X2
           have i₂ := b0e156 X0
           grind)
        | exact superpose b0e156 b0e673
        | exact resolve b0e673 b0e156
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e156 b0e673
      have b0e696 : ∀ X1 X3 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op X1 X3)) (M.op x y)) := by
        intro X1 X3
        first
        | (have i₁ := b0e681 X1 X3
           have i₂ := b0e226 X1 y
           grind)
        | exact superpose b0e226 b0e681
        | exact resolve b0e681 b0e226
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e226 b0e681
      have b0e708 : ∀ X1 X3 : G, (M.op x y) = (M.op (M.op x (M.op X1 X3)) (M.op x y)) := by
        intro X1 X3
        first
        | (have i₁ := b0e696 X1 X3
           have i₂ := b0e460
           grind)
        | exact superpose b0e460 b0e696
        | exact resolve b0e696 b0e460
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e696
      have b0e745 : ∀ X0 X1 : G, (M.op (M.op y x) (M.op x X0)) = (M.op x (M.op X1 (M.op x X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e34 X1 x X0 x
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e34
        | exact resolve b0e34 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e793 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X4) (M.op X0 X3)) = (M.op X0 (M.op (M.op X5 (M.op X0 X5)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e34 (M.op X5 (M.op X0 X5)) X0 X3 X4
           have i₂ := b0e34 X5 X0 X1 X2
           grind)
        | exact superpose b0e34 b0e34
        | exact resolve b0e34 b0e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e884 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X3) X4) (M.op X0 X3)) = (M.op X0 (M.op (M.op x y) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1)))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e793 X0 X1 X2 X3 X4 x
           have i₂ := b0e652 x X0 (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))
           grind)
        | exact superpose b0e652 b0e793
        | exact resolve b0e793 b0e652
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e652 b0e793
      have b0e918 : ∀ X0 : G, (M.op x (M.op y x)) = (M.op (M.op y x) (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e745 X0 x
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e745
        | exact resolve b0e745 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e745
      have b0e953 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 X3) X4) (M.op X0 X3)) = (M.op X0 (M.op (M.op x y) (M.op x (M.op X0 X1)))) := by
        intro X0 X1 X3 X4
        first
        | (have i₁ := b0e884 X0 X1 x X3 X4
           have i₂ := b0e692 (M.op X0 X1) x
           grind)
        | exact superpose b0e692 b0e884
        | exact resolve b0e884 b0e692
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e692 b0e884
      have b0e980 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op x (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e918 X0
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e918
        | exact resolve b0e918 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e918
      have b0e1006 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X0 X3)) (M.op y x)) = (M.op X0 (M.op (M.op x y) (M.op x (M.op X0 X1)))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e953 X0 X1 X3 x
           have i₂ := b0e47 (M.op X0 X3) x
           grind)
        | exact superpose b0e47 b0e953
        | exact resolve b0e953 b0e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47 b0e953
      have b0e1026 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e980 X0
           have i₂ := b0e460
           grind)
        | exact superpose b0e460 b0e980
        | exact resolve b0e980 b0e460
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460 b0e980
      have b0e1036 : ∀ X0 X1 X3 : G, (M.op (M.op x (M.op X0 X3)) (M.op x y)) = (M.op X0 (M.op (M.op x y) (M.op x (M.op X0 X1)))) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e1006 X0 X1 X3
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e1006
        | exact resolve b0e1006 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e1006
      have b0e1053 : ∀ X0 X3 : G, (M.op (M.op x (M.op X0 X3)) (M.op x y)) = (M.op X0 (M.op x y)) := by
        intro X0 X3
        first
        | (have i₁ := b0e1036 X0 x X3
           have i₂ := b0e1026 (M.op X0 x)
           grind)
        | exact superpose b0e1026 b0e1036
        | exact resolve b0e1036 b0e1026
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1026 b0e1036
      have b0e1064 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e1053 X0 x
           have i₂ := b0e708 X0 x
           grind)
        | exact superpose b0e708 b0e1053
        | exact resolve b0e1053 b0e708
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e708 b0e1053
      have b0e1086 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
      have b0e1101 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 (M.op x y) x X0 X1
           have i₂ := b0e1064 (M.op (M.op x y) x)
           grind)
        | exact superpose b0e1064 b0e33
        | exact resolve b0e33 b0e1064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e1121 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e1101 X0 X1
           have i₂ := b0e1064 (M.op (M.op x y) X0)
           grind)
        | exact superpose b0e1064 b0e1101
        | exact resolve b0e1101 b0e1064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1101
      have b0e1540 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e35 x
           have i₂ := b0e1121 (σ x) x
           grind)
        | exact superpose b0e1121 b0e35
        | exact resolve b0e35 b0e1121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e1121
      have b0e2046 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1540
           grind)
        | exact superpose b0e1540 b0e18
        | exact resolve b0e18 b0e1540
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1540
      have b0e5626 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e71 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71
      have b0e5627 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e5626 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5626
      have b0e56003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e5627 (M.op x y)
           have i₂ := b0e1086
           grind)
        | exact superpose b0e1086 b0e5627
        | (have j0 := b0e5627 (M.op x y)
           grind)
        | exact resolve b0e5627 b0e1086
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1086 b0e5627
      have b0e56012 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e56003
      have b0e60994 : ∀ X0 : G, (M.op X0 (M.op (M.op x X0) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e618 (σ (M.op x y)) (σ (M.op x y)) X0
           have i₂ := b0e56012
           grind)
        | exact superpose b0e56012 b0e618
        | exact resolve b0e618 b0e56012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e618
      have b0e61027 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (M.op x X0) (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b0e60994 X0
           have i₂ := b0e56012
           grind)
        | exact superpose b0e56012 b0e60994
        | exact resolve b0e60994 b0e56012
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56012 b0e60994
      have b0e61109 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e61027 X0
           have i₂ := b0e1064 (M.op x X0)
           grind)
        | exact superpose b0e1064 b0e61027
        | exact resolve b0e61027 b0e1064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61027
      have b0e61164 : (M.op x y) = (σ (M.op x y)) := by
        first
        | (have i₁ := b0e61109 x
           have i₂ := b0e1064 x
           grind)
        | exact superpose b0e1064 b0e61109
        | exact resolve b0e61109 b0e1064
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1064 b0e61109
      have b0e61188 : False := by grind
      exact b0e61188
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e25 : (σ y) = (k (σ y) (σ y)) := by grind
        have b1e26 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e25
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e25
          | exact resolve b1e25 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25
        have b1e31 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (k y y)
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e13
          | exact resolve b1e13 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : y = (k y y) := by
          first
          | (have i₁ := b1e31
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e31
          | exact resolve b1e31 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31
        have b1e37 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e12 x X0 X3
             have i₂ := b1e12 x X0 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e44 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b1e41 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e41
          | exact resolve b1e41 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e45 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e37 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e37
          | exact resolve b1e37 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e46 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b1e42 x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e42
          | exact resolve b1e42 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e78 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e32
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e32 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e81 : y = (M.op y y) := by grind
        clear b1e78
        have b1e86 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e12 X0 y y
             have i₂ := b1e81
             grind)
          | exact superpose b1e81 b1e12
          | exact resolve b1e12 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e88 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e86 X0
             have i₂ := b1e81
             grind)
          | exact superpose b1e81 b1e86
          | exact resolve b1e86 b1e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e81 b1e86
        have b1e98 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op (σ y) X0) X0 X1
             have i₂ := b1e44 X0
             grind)
          | exact superpose b1e44 b1e12
          | exact resolve b1e12 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e99 : (M.op y x) = (M.op (M.op (σ y) x) (σ y)) := by
          first
          | (have i₁ := b1e42 (M.op (σ y) x)
             have i₂ := b1e44 x
             grind)
          | exact superpose b1e44 b1e42
          | exact resolve b1e42 b1e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42 b1e44
        have b1e100 : (σ y) = (M.op y x) := by
          first
          | (have i₁ := b1e99
             have i₂ := b1e45 x
             grind)
          | exact superpose b1e45 b1e99
          | exact resolve b1e99 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e99
        have b1e101 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e98 X0 X1
             have i₂ := b1e45 X0
             grind)
          | exact superpose b1e45 b1e98
          | exact resolve b1e98 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45 b1e98
        have b1e116 : ∀ X1 : G, y = (M.op (M.op y X1) y) := by
          intro X1
          first
          | (have i₁ := b1e12 x y X1
             have i₂ := b1e88 x
             grind)
          | exact superpose b1e88 b1e12
          | exact resolve b1e12 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e123 : y = (σ y) := by
          first
          | (have i₁ := b1e116 x
             have i₂ := b1e101 y x
             grind)
          | exact superpose b1e101 b1e116
          | exact resolve b1e116 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116
        have b1e141 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e123
             grind)
          | exact superpose b1e123 b1e19
          | exact resolve b1e19 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e146 : (M.op (σ x) y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e141
             have i₂ := b1e46
             grind)
          | exact superpose b1e46 b1e141
          | exact resolve b1e141 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46 b1e141
        have b1e147 : (M.op (σ x) y) ≠ (σ (σ y)) := by
          first
          | (have i₁ := b1e146
             have i₂ := b1e100
             grind)
          | exact superpose b1e100 b1e146
          | exact resolve b1e146 b1e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e100 b1e146
        have b1e148 : (σ y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e147
             have i₂ := b1e123
             grind)
          | exact superpose b1e123 b1e147
          | exact resolve b1e147 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e147
        have b1e149 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e148
             have i₂ := b1e123
             grind)
          | exact superpose b1e123 b1e148
          | exact resolve b1e148 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148
        have b1e195 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e38 X0 X1 (M.op y X0)
             have i₂ := b1e88 X0
             grind)
          | exact superpose b1e88 b1e38
          | exact resolve b1e38 b1e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e230 : ∀ X0 : G, (σ y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e195 X0 x
             have i₂ := b1e101 X0 x
             grind)
          | exact superpose b1e101 b1e195
          | exact resolve b1e195 b1e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101 b1e195
        have b1e257 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e230 X0
             have i₂ := b1e123
             grind)
          | exact superpose b1e123 b1e230
          | exact resolve b1e230 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123 b1e230
        have b1e322 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e88 X0
             have i₂ := b1e257 X0
             grind)
          | exact superpose b1e257 b1e88
          | exact resolve b1e88 b1e257
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e88 b1e257
        have b1e972 : y ≠ y := by
          first
          | (have i₁ := b1e149
             have i₂ := b1e322 (σ x)
             grind)
          | exact superpose b1e322 b1e149
          | (have r₁ := b1e149
             have r₂ := b1e322 (σ x)
             grind)
          | exact resolve b1e149 b1e322
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e149 b1e322
        have b1e973 : False := by grind
        exact b1e973
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
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
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 (M.op X0 X2) X2 X3
             have i₂ := b2e12 X2 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 X3 (M.op X0 X3)
             have i₂ := b2e12 X3 X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X0 X1 x
             have i₂ := b2e12 X2 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e37 : ∀ X1 : G, (M.op y x) = (M.op (M.op x X1) x) := by
          intro X1
          first
          | (have i₁ := b2e12 x x X1
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x X0) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op x X0) X0 X1
             have i₂ := b2e30 X0
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 X0 X0
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e66 : (M.op y x) = (M.op (M.op y x) x) := by
          first
          | (have i₁ := b2e37 (M.op x x)
             have i₂ := b2e30 x
             grind)
          | exact superpose b2e30 b2e37
          | exact resolve b2e37 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e85 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e174 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x X1) X0)) = (M.op x (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e33 X0 (M.op x X1) x
             have i₂ := b2e37 X1
             grind)
          | exact superpose b2e37 b2e33
          | exact resolve b2e33 b2e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e37
        have b2e294 : ∀ X0 X1 X2 : G, (M.op y x) = (M.op X0 (M.op (M.op x (M.op (M.op X1 X2) X1)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e30 (M.op (M.op X1 X2) X1)
             have i₂ := b2e31 X1 X2 X0 (M.op x (M.op (M.op X1 X2) X1))
             grind)
          | exact superpose b2e31 b2e30
          | exact resolve b2e30 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e295 : (M.op y x) = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b2e294 x x x
             have i₂ := b2e174 x (M.op (M.op x x) x)
             grind)
          | exact superpose b2e174 b2e294
          | exact resolve b2e294 b2e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174 b2e294
        have b2e302 : (M.op y x) = (M.op (M.op y x) (M.op y x)) := by
          first
          | (have i₁ := b2e30 (M.op y x)
             have i₂ := b2e295
             grind)
          | exact superpose b2e295 b2e30
          | exact resolve b2e30 b2e295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e304 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b2e33 x y X0
             have i₂ := b2e295
             grind)
          | exact superpose b2e295 b2e33
          | exact resolve b2e33 b2e295
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e295
        have b2e350 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X3 X2) (M.op (M.op X3 X4) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e27 X3 X4 X2 (M.op X1 X2)
             have i₂ := b2e33 X2 X1 X0
             grind)
          | (have i₁ := b2e27 X3 X4 X2 (M.op X1 X2)
             have i₂ := b2e33 X0 X1 X2
             grind)
          | exact superpose b2e33 b2e27
          | exact resolve b2e27 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33
        have b2e353 : ∀ X0 X1 X2 : G, (M.op (M.op y x) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e27 X1 X2 X0 (M.op y X0)
             have i₂ := b2e304 X0
             grind)
          | exact superpose b2e304 b2e27
          | exact resolve b2e27 b2e304
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e304
        have b2e404 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op y x) X0) (M.op (M.op y x) (M.op y x))) := by
          intro X0 X1
          first
          | (have i₁ := b2e27 (M.op y x) x X0 X1
             have i₂ := b2e66
             grind)
          | exact superpose b2e66 b2e27
          | exact resolve b2e27 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e66
        have b2e448 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op y x) X0) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e404 X0 X1
             have i₂ := b2e302
             grind)
          | exact superpose b2e302 b2e404
          | exact resolve b2e404 b2e302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e404
        have b2e467 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op y x) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e350 X0 X1 X2 x x
             have i₂ := b2e353 X2 x x
             grind)
          | exact superpose b2e353 b2e350
          | exact resolve b2e350 b2e353
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e350 b2e353
        have b2e473 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x (M.op y x)) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e448 X0 X1
             have i₂ := b2e39 (M.op y x) X0
             grind)
          | exact superpose b2e39 b2e448
          | exact resolve b2e448 b2e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39 b2e448
        have b2e484 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y x) (M.op y x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e473 X0 X1
             have i₂ := b2e467 x y (M.op y x)
             grind)
          | exact superpose b2e467 b2e473
          | exact resolve b2e473 b2e467
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e467 b2e473
        have b2e490 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y x) := by
          intro X0 X1
          first
          | (have i₁ := b2e484 X0 X1
             have i₂ := b2e302
             grind)
          | exact superpose b2e302 b2e484
          | exact resolve b2e484 b2e302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e302 b2e484
        have b2e1785 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e53 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53
        have b2e1786 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1785
             have r₂ := b2e22
             grind)
          | exact resolve b2e1785 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1785
        have b2e1787 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1786
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1786
          | exact resolve b2e1786 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1786
        have b2e1788 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1787
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1787
          | exact resolve b2e1787 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1787
        have b2e1802 : (M.op (σ x) (σ x)) = (M.op y x) := by
          first
          | (have i₁ := b2e490 (σ x) (σ y)
             have i₂ := b2e1788
             grind)
          | exact superpose b2e1788 b2e490
          | exact resolve b2e490 b2e1788
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e490
        have b2e1830 : (σ x) = (k (σ x) (M.op y x)) := by grind
        have b2e3150 : (k x (τ (M.op y x))) = (τ (σ x)) := by
          first
          | (have i₁ := b2e85 x (M.op y x)
             have i₂ := b2e1830
             grind)
          | exact superpose b2e1830 b2e85
          | exact resolve b2e85 b2e1830
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85 b2e1830
        have b2e3151 : x = (k x (τ (M.op y x))) := by
          first
          | (have i₁ := b2e3150
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e3150
          | exact resolve b2e3150 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3150
        have b2e3906 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e62 x x
             grind)
          | exact superpose b2e62 b2e21
          | (have j1 := b2e62 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e62 x y
             grind)
          | exact resolve b2e21 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62
        have b2e4054 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e3906
        have b2e4138 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op y x) := by
          first
          | (have i₁ := b2e4054
             have i₂ := b2e1802
             grind)
          | exact superpose b2e1802 b2e4054
          | exact resolve b2e4054 b2e1802
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1802 b2e4054
        have b2e11798 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4138
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e4138
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e4138 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4138
        have b2e11806 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op y x) ∨ x = (M.op x x) := by grind
        clear b2e11798
        have b2e11818 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op y x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e11806
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11806
          | exact resolve b2e11806 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11806
        have b2e11819 : (σ x) = (M.op y x) ∨ x = (M.op x x) := by grind
        clear b2e11818
        have b2e11827 : (σ x) = (M.op y x) ∨ x = y := by
          first
          | (have i₁ := b2e11819
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e11819
          | exact resolve b2e11819 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11819
        have b2e11848 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3151
             have i₂ := b2e11827
             grind)
          | exact superpose b2e11827 b2e3151
          | exact resolve b2e3151 b2e11827
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3151 b2e11827
        have b2e11913 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e11848
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e11848
          | exact resolve b2e11848 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11848
        have b2e12106 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e11913
             grind)
          | exact superpose b2e11913 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e11913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e11913
        have b2e12115 : x = (M.op x x) ∨ x = y := by grind
        clear b2e12106
        have b2e12130 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e12115
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12115
          | exact resolve b2e12115 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e12115
        have b2e12131 : x = y := by grind
        clear b2e12130
        have b2e12286 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e1788
             have i₂ := b2e12131
             grind)
          | exact superpose b2e12131 b2e1788
          | exact resolve b2e1788 b2e12131
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1788 b2e12131
        have b2e12298 : False := by grind
        exact b2e12298
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : y = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e38 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b3e12 x X0 X3
             have i₂ := b3e12 x X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e41 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 x
             have i₂ := b3e12 X2 X1 x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b3e42 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e42
          | exact resolve b3e42 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e49 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (M.op y X1)
             have i₂ := b3e44 X1
             grind)
          | exact superpose b3e44 b3e12
          | exact resolve b3e12 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e50 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op y X0) X0 X1
             have i₂ := b3e44 X0
             grind)
          | exact superpose b3e44 b3e12
          | exact resolve b3e12 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b3e88 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y X0) y) := by
          intro X0
          first
          | (have i₁ := b3e49 (M.op y X0) X0
             have i₂ := b3e44 X0
             grind)
          | exact superpose b3e44 b3e49
          | exact resolve b3e49 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e97 : ∀ X0 X2 : G, (M.op y X0) = (M.op (M.op X0 X2) X0) := by
          intro X0 X2
          first
          | (have i₁ := b3e12 x X0 X2
             have i₂ := b3e49 x X0
             grind)
          | exact superpose b3e49 b3e12
          | exact resolve b3e12 b3e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e106 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e88 X0
             have i₂ := b3e97 y X0
             grind)
          | exact superpose b3e97 b3e88
          | exact resolve b3e88 b3e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88 b3e97
        have b3e109 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e106 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e106
          | exact resolve b3e106 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e119 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e44 X0
             have i₂ := b3e109 X0
             grind)
          | exact superpose b3e109 b3e44
          | exact resolve b3e44 b3e109
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44 b3e109
        have b3e201 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ y) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e38 (σ x) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e38
          | exact resolve b3e38 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e225 : (M.op (σ y) (σ x)) = (M.op (M.op y (σ x)) y) := by
          first
          | (have i₁ := b3e201 x
             have i₂ := b3e50 (σ x) x
             grind)
          | exact superpose b3e50 b3e201
          | exact resolve b3e201 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50 b3e201
        have b3e243 : y = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e225
             have i₂ := b3e119 (M.op y (σ x))
             grind)
          | exact superpose b3e119 b3e225
          | exact resolve b3e225 b3e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e225
        have b3e296 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b3e43 X0 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e43
          | exact resolve b3e43 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e340 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e296 x
             have i₂ := b3e41 x
             grind)
          | exact superpose b3e41 b3e296
          | exact resolve b3e296 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e296
        have b3e373 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e340
             have i₂ := b3e243
             grind)
          | exact superpose b3e243 b3e340
          | exact resolve b3e340 b3e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e340
        have b3e430 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) X0) (M.op (σ y) (σ x))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op (σ x) X0) X0 X1
             have i₂ := b3e41 X0
             grind)
          | exact superpose b3e41 b3e12
          | exact resolve b3e12 b3e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e41
        have b3e447 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ x) X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b3e430 X0 X1
             have i₂ := b3e243
             grind)
          | exact superpose b3e243 b3e430
          | exact resolve b3e430 b3e243
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e243 b3e430
        have b3e465 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e447 X0 X1
             have i₂ := b3e119 (M.op (σ x) X0)
             grind)
          | exact superpose b3e119 b3e447
          | exact resolve b3e447 b3e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e447
        have b3e476 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e373
             grind)
          | exact superpose b3e373 b3e19
          | exact resolve b3e19 b3e373
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e490 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e476
             have i₂ := b3e119 x
             grind)
          | exact superpose b3e119 b3e476
          | exact resolve b3e476 b3e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119 b3e476
        have b3e5646 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e77 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e77
          | exact resolve b3e77 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e5865 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e5646
        have b3e7468 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e5865
             grind)
          | exact superpose b3e5865 b3e13
          | exact resolve b3e13 b3e5865
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e5865
        have b3e7485 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e7468
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e7468
          | exact resolve b3e7468 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7468
        have b3e7503 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e7485
             grind)
          | exact superpose b3e7485 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e7485
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7485
        have b3e7513 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e7503
        have b3e7523 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e7513
             have r₂ := b3e20
             grind)
          | exact resolve b3e7513 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7513
        have b3e7806 : y = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e465 x x
             have i₂ := b3e7523
             grind)
          | exact superpose b3e7523 b3e465
          | exact resolve b3e465 b3e7523
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e465 b3e7523
        have b3e7808 : (σ x) = (σ y) := by
          first
          | (have r₁ := b3e7806
             have r₂ := b3e20
             grind)
          | exact resolve b3e7806 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7806
        have b3e7928 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e7808
             grind)
          | exact superpose b3e7808 b3e22
          | exact resolve b3e22 b3e7808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e7936 : y = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e373
             have i₂ := b3e7808
             grind)
          | exact superpose b3e7808 b3e373
          | exact resolve b3e373 b3e7808
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e373 b3e7808
        have b3e7961 : y = (σ y) := by
          first
          | (have i₁ := b3e7928
             have i₂ := b3e7936
             grind)
          | exact superpose b3e7936 b3e7928
          | exact resolve b3e7928 b3e7936
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e7928 b3e7936
        have b3e7968 : False := by grind
        exact b3e7968
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ y) (σ y) X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e13 x X0 X3
               have i₂ := b4e13 x X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e46 : ∀ X0 : G, y = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b4e44 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e44
            | exact resolve b4e44 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e47 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e43 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e43
            | exact resolve b4e43 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e48 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e39 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e98 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ y) X0) (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op (σ y) X0) X0 X1
               have i₂ := b4e47 X0
               grind)
            | exact superpose b4e47 b4e13
            | exact resolve b4e13 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : y = (M.op (M.op (σ y) y) (σ y)) := by
            first
            | (have i₁ := b4e46 (M.op (σ y) y)
               have i₂ := b4e47 y
               grind)
            | exact superpose b4e47 b4e46
            | exact resolve b4e46 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e101 : y = (σ y) := by
            first
            | (have i₁ := b4e100
               have i₂ := b4e48 y
               grind)
            | exact superpose b4e48 b4e100
            | exact resolve b4e100 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100
          have b4e102 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e98 X0 X1
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e98
            | exact resolve b4e98 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48 b4e98
          have b4e105 : ∀ X0 X1 : G, y = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e102 X0 X1
               have i₂ := b4e101
               grind)
            | exact superpose b4e101 b4e102
            | exact resolve b4e102 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e102
          have b4e117 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e101
               grind)
            | exact superpose b4e101 b4e20
            | exact resolve b4e20 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e187 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e40 X0 X1 (M.op y X0)
               have i₂ := b4e46 X0
               grind)
            | exact superpose b4e46 b4e40
            | exact resolve b4e40 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e225 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e187 X0 x
               have i₂ := b4e105 X0 x
               grind)
            | exact superpose b4e105 b4e187
            | exact resolve b4e187 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105 b4e187
          have b4e272 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e46 X0
               have i₂ := b4e225 X0
               grind)
            | exact superpose b4e225 b4e46
            | exact resolve b4e46 b4e225
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46 b4e225
          have b4e2598 : (σ y) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e117
               have i₂ := b4e272 x
               grind)
            | exact superpose b4e272 b4e117
            | exact resolve b4e117 b4e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e117
          have b4e2599 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e2598
               have i₂ := b4e272 (σ x)
               grind)
            | exact superpose b4e272 b4e2598
            | exact resolve b4e2598 b4e272
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e272 b4e2598
          have b4e2600 : False := by grind
          exact b4e2600
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e26 : y = (k y y) := by grind
          have b5e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
          have b5e5259 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e73 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73
          have b5e5260 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e5259 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e5259
          have b5e9189 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e5260 y
               have i₂ := b5e26
               grind)
            | exact superpose b5e26 b5e5260
            | (have j0 := b5e5260 y
               grind)
            | exact resolve b5e5260 b5e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26 b5e5260
          have b5e9196 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e9189
          have b5e9216 : False := by grind
          exact b5e9216
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : y ≠ (M.op y y) := by grind
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
        have b6e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b6e88 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e92 : x = (M.op x y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e88
             have r₂ := b6e20
             grind)
          | exact resolve b6e88 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
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
        have b6e97 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 x y
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e12
          | exact resolve b6e12 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e172 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b6e97 y
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e97
          | exact resolve b6e97 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e216 : x = (k x (M.op y x)) := by grind
        have b6e3370 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e86 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e86
          | exact resolve b6e86 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e86
        have b6e3588 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e3370
        have b6e4342 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e3588
             grind)
          | exact superpose b6e3588 b6e13
          | exact resolve b6e13 b6e3588
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e4359 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4342
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e4342
          | exact resolve b6e4342 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4342
        have b6e4384 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e4359
             grind)
          | exact superpose b6e4359 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e4359
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4359
        have b6e4392 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e4384
        have b6e4400 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e4392
             have r₂ := b6e20
             grind)
          | exact resolve b6e4392 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e4392
        have b6e4414 : x = (M.op y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e4400
             have i₂ := b6e172
             grind)
          | exact superpose b6e172 b6e4400
          | exact resolve b6e4400 b6e172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e172 b6e4400
        have b6e4766 : x = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e216
             have i₂ := b6e4414
             grind)
          | exact superpose b6e4414 b6e216
          | exact resolve b6e216 b6e4414
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e216 b6e4414
        have b6e8552 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e3588
             have i₂ := b6e4766
             grind)
          | exact superpose b6e4766 b6e3588
          | exact resolve b6e3588 b6e4766
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3588 b6e4766
        have b6e8563 : (σ x) = (σ y) := by grind
        clear b6e8552
        have b6e8632 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e8563
             grind)
          | exact superpose b6e8563 b6e13
          | exact resolve b6e13 b6e8563
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8563
        have b6e8647 : x = y := by
          first
          | (have i₁ := b6e8632
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e8632
          | exact resolve b6e8632 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e8632
        have b6e9066 : y = (M.op y y) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e8647
             grind)
          | exact superpose b6e8647 b6e95
          | exact resolve b6e95 b6e8647
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95 b6e8647
        have b6e9108 : False := by grind
        exact b6e9108
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op y y) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e26 : (σ y) = (k (σ y) (σ y)) := by grind
          have b7e27 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e26
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e26
            | exact resolve b7e26 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26
          have b7e32 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e27
               grind)
            | exact superpose b7e27 b7e14
            | exact resolve b7e14 b7e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : y = (k y y) := by
            first
            | (have i₁ := b7e32
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e32
            | exact resolve b7e32 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e32
          have b7e91 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e33
               have i₂ := b7e18 y y
               grind)
            | exact superpose b7e18 b7e33
            | (have j1 := b7e18 y y
               grind)
            | exact resolve b7e33 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e33
          have b7e94 : y = (M.op y y) := by grind
          clear b7e91
          have b7e98 : False := by grind
          exact b7e98
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : y ≠ (M.op y y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1183 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e56 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e1184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1183
               have r₂ := b8e24
               grind)
            | exact resolve b8e1183 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1183
          have b8e1185 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1184
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1184
            | exact resolve b8e1184 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1184
          have b8e1186 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1185
               grind)
            | exact superpose b8e1185 b8e20
            | exact resolve b8e20 b8e1185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1185
          have b8e1206 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1186
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1186
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1186 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1186
          have b8e1207 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1206
          have b8e1210 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1207
               have r₂ := b8e21
               grind)
            | exact resolve b8e1207 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1207
          have b8e1213 : False := by grind
          exact b8e1213
