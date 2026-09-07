import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e30 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0 (M.op X1 x)
           have i₂ := b0e11 X0 X1 x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e30 x X0
           have i₂ := b0e30 x X1
           grind)
        | exact superpose b0e30 b0e30
        | exact resolve b0e30 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op X0 (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e23
           have i₂ := b0e30 X0 (σ x)
           grind)
        | exact superpose b0e30 b0e23
        | exact resolve b0e23 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e41 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X1 X1
           have i₂ := b0e30 X1 X0
           grind)
        | exact superpose b0e30 b0e11
        | exact resolve b0e11 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e46 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) := by
        intro X0
        first
        | (have i₁ := b0e37 X0
           have i₂ := b0e41 X0 X0
           grind)
        | exact superpose b0e41 b0e37
        | exact resolve b0e37 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e41
      have b0e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X0
           have i₂ := b0e36 X0 X1
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e36 X0 X1
           grind)
        | exact superpose b0e36 b0e14
        | (have j0 := b0e14 X0 X0
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e36 X1 X1
           grind)
        | (have r₁ := b0e14 X0 X0
           have r₂ := b0e36 X0 X0
           grind)
        | exact resolve b0e14 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e88 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e78 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e78
      have b0e159 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X1
           have i₂ := b0e88 X0 (σ X1)
           grind)
        | exact superpose b0e88 b0e17
        | exact resolve b0e17 b0e88
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e163 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e159 X0 X1
           have i₂ := b0e84 X1
           grind)
        | exact superpose b0e84 b0e159
        | exact resolve b0e159 b0e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e84 b0e159
      have b0e244 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e46 X1
           have i₂ := b0e36 x X0
           grind)
        | (have i₁ := b0e46 X1
           have i₂ := b0e36 X0 x
           grind)
        | exact superpose b0e36 b0e46
        | exact resolve b0e46 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e46
      have b0e245 : False := by grind
      exact b0e245
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e35 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0 (M.op X1 x)
             have i₂ := b2e12 X0 X1 x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e35 x X0
             have i₂ := b2e35 x X1
             grind)
          | exact superpose b2e35 b2e35
          | exact resolve b2e35 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35
        have b2e76 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e41 X0 X1
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e41 X0 X1
             grind)
          | exact superpose b2e41 b2e15
          | (have j0 := b2e15 X0 X0
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e41 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e41 X0 X0
             grind)
          | exact resolve b2e15 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e83 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e78 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e78
        have b2e88 : (k x y) = (M.op y y) := by grind
        clear b2e76
        have b2e94 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e83 (σ X0)
             grind)
          | exact superpose b2e83 b2e18
          | exact resolve b2e18 b2e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e94 X0
             have i₂ := b2e83 X0
             grind)
          | exact superpose b2e83 b2e94
          | exact resolve b2e94 b2e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e94
        have b2e106 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e106 X0 X1
             have i₂ := b2e97 X0
             grind)
          | exact superpose b2e97 b2e106
          | (have j0 := b2e106 X0 X1
             grind)
          | exact resolve b2e106 b2e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e97 b2e106
        have b2e162 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X1
             have i₂ := b2e86 X0 (σ X1)
             grind)
          | exact superpose b2e86 b2e18
          | exact resolve b2e18 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e166 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e162 X0 X1
             have i₂ := b2e83 X1
             grind)
          | exact superpose b2e83 b2e162
          | exact resolve b2e162 b2e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83 b2e162
        have b2e2166 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e124 x y
             grind)
          | exact superpose b2e124 b2e21
          | (have j1 := b2e124 x y
             grind)
          | exact resolve b2e21 b2e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124
        have b2e2233 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e2166
             have r₂ := b2e24
             grind)
          | exact resolve b2e2166 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e2166
        have b2e2257 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e2233
             have r₂ := b2e22
             grind)
          | exact resolve b2e2233 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2233
        have b2e2267 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e2257
             have i₂ := b2e88
             grind)
          | exact superpose b2e88 b2e2257
          | exact resolve b2e2257 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e88 b2e2257
        have b2e2271 : False := by grind
        exact b2e2271
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
          intro X0 X1 X2
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X0 (M.op X1 x)
             have i₂ := b6e12 X0 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e34 x X0
             have i₂ := b6e34 x X1
             grind)
          | exact superpose b6e34 b6e34
          | exact resolve b6e34 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e24
             have i₂ := b6e34 X0 (σ x)
             grind)
          | exact superpose b6e34 b6e24
          | exact resolve b6e24 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e45 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X1 X1 X1
             have i₂ := b6e34 X1 X0
             grind)
          | exact superpose b6e34 b6e12
          | exact resolve b6e12 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34
        have b6e50 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b6e41 X0
             have i₂ := b6e45 X0 X0
             grind)
          | exact superpose b6e45 b6e41
          | exact resolve b6e41 b6e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41 b6e45
        have b6e86 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e88 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e86
        have b6e93 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e88
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e88
          | exact resolve b6e88 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e224 : ∀ X0 : G, (M.op X0 X0) = (σ (k x y)) := by
          intro X0
          first
          | (have i₁ := b6e40 X0 (σ y)
             have i₂ := b6e93
             grind)
          | exact superpose b6e93 b6e40
          | exact resolve b6e40 b6e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e93
        have b6e324 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b6e224 X0
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e224
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e224 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e224
        have b6e359 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ x = y := by
          intro X0
          first
          | (have j0 := b6e324 X0
             grind)
          | (have r₁ := b6e324 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e324 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e324
        have b6e365 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
          intro X0
          first
          | (have j0 := b6e359 X0
             grind)
          | (have r₁ := b6e359 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e359 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e359
        have b6e367 : False := by grind
        exact b6e367
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e31 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0 (M.op X1 x)
               have i₂ := b8e13 X0 X1 x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e37 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e31 x X0
               have i₂ := b8e31 x X1
               grind)
            | exact superpose b8e31 b8e31
            | exact resolve b8e31 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e73 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e37 X0 X1
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e37 X0 X1
               grind)
            | exact superpose b8e37 b8e16
            | (have j0 := b8e16 X0 X0
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e37 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e37 X0 X0
               grind)
            | exact resolve b8e16 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e73 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e88 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e78 (σ X0)
               grind)
            | exact superpose b8e78 b8e19
            | exact resolve b8e19 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e88 X0
               have i₂ := b8e78 X0
               grind)
            | exact superpose b8e78 b8e88
            | exact resolve b8e88 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e97 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e103 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X2) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e37 X2 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e37 X0 X1
               have i₂ := b8e18 X1 X1
               grind)
            | exact superpose b8e18 b8e37
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e37 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37
          have b8e107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e16 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 (M.op X0 X0) (M.op X0 X1)
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e110 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e107 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e97 X0 X1
               have i₂ := b8e89 X0
               grind)
            | exact superpose b8e89 b8e97
            | (have j0 := b8e97 X0 X1
               grind)
            | exact resolve b8e97 b8e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89 b8e97
          have b8e136 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X1
               have i₂ := b8e81 X0 (σ X1)
               grind)
            | exact superpose b8e81 b8e19
            | exact resolve b8e19 b8e81
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e139 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e136 X0 X1
               have i₂ := b8e78 X1
               grind)
            | exact superpose b8e78 b8e136
            | exact resolve b8e136 b8e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78 b8e136
          have b8e937 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e110 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e941 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e937 X0 X1
               have j1 := b8e103 X0 X1 x
               grind)
            | (have r₁ := b8e937 X0 x
               have r₂ := b8e103 X0 x x
               grind)
            | (have r₁ := b8e937 X1 X1
               have r₂ := b8e103 X1 X1 X1
               grind)
            | (have r₁ := b8e937 X0 X1
               have r₂ := b8e103 (M.op X0 X1) (M.op X1 X1) x
               grind)
            | exact resolve b8e937 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103 b8e937
          have b8e2273 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e114 x y
               grind)
            | exact superpose b8e114 b8e20
            | (have j1 := b8e114 x y
               grind)
            | exact resolve b8e20 b8e114
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e2344 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e2273
               have r₂ := b8e24
               grind)
            | exact resolve b8e2273 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2273
          have b8e77030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e2344
               have i₂ := b8e941 x y
               grind)
            | exact superpose b8e941 b8e2344
            | (have j1 := b8e941 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e2344
               have r₂ := b8e941 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e2344
               have r₂ := b8e941 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e2344 b8e941
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e941 b8e2344
          have b8e77031 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e77030
          have b8e77035 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e77031
               have r₂ := b8e22
               grind)
            | exact resolve b8e77031 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77031
          have b8e77040 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e77035
               grind)
            | exact superpose b8e77035 b8e23
            | exact resolve b8e23 b8e77035
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77035
          have b8e77138 : False := by grind
          exact b8e77138

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxx_pxx_pxy_Equation3274 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
      have b0e43 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e45
      have b0e48 : (M.op x x) = (k x y) := by grind
      clear b0e43
      have b0e49 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e47
        | exact resolve b0e47 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e50 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e49
        | exact resolve b0e49 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e49
      have b0e51 : False := by grind
      exact b0e51
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e26 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y (M.op x x))) := by
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
        have b1e27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X1 X0) X2 X0
             have i₂ := b1e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e56 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e56
        have b1e60 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e60
          | exact resolve b1e60 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e60
        have b1e149 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e23
          | exact resolve b1e23 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e61
        have b1e256 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e28 X1 x X3
             have i₂ := b1e28 X1 x X0
             grind)
          | (have i₁ := b1e28 X0 X0 x
             have i₂ := b1e28 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e3374 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 X1 x X2
             have i₂ := b1e256 (M.op X1 (M.op x X1)) X1 X0
             grind)
          | (have i₁ := b1e29 X1 x X2
             have i₂ := b1e256 X0 X1 (M.op X1 (M.op x X1))
             grind)
          | exact superpose b1e256 b1e29
          | exact resolve b1e29 b1e256
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e256
        have b1e5435 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e26 x
             have i₂ := b1e3374 y x x
             grind)
          | exact superpose b1e3374 b1e26
          | exact resolve b1e26 b1e3374
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e3374
        have b1e6658 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e149
             have i₂ := b1e5435
             grind)
          | exact superpose b1e5435 b1e149
          | exact resolve b1e149 b1e5435
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e149 b1e5435
        have b1e6703 : False := by grind
        exact b1e6703
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e54 : (M.op x x) = (k x y) := by grind
        clear b2e51
        have b2e95 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e96 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X1 X0
             have j1 := b2e17 X1 X0
             grind)
          | (have r₁ := b2e15 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e15 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e15 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e99 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e114 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e95 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e95
        have b2e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e96 X0 X1
             have j1 := b2e15 X1 X0
             grind)
          | (have r₁ := b2e96 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e96 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e96 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e124 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e114 X0 X1
             have j1 := b2e15 X1 X0
             grind)
          | (have r₁ := b2e114 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | (have r₁ := b2e114 X1 X0
             have r₂ := b2e15 X0 X1
             grind)
          | exact resolve b2e114 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114
        have b2e130 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e124 X0 X1
             have j1 := b2e123 X0 X1
             grind)
          | (have r₁ := b2e124 X0 X1
             have r₂ := b2e123 X0 X1
             grind)
          | (have r₁ := b2e124 X1 X0
             have r₂ := b2e123 X0 X1
             grind)
          | exact resolve b2e124 b2e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e123 b2e124
        have b2e427 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e130 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130
        have b2e2199 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e2200 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j1 := b2e427 (σ x) (σ y)
             grind)
          | (have r₁ := b2e2199
             have r₂ := b2e427 (σ x) (σ y)
             grind)
          | exact resolve b2e2199 b2e427
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e427 b2e2199
        have b2e2201 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e2200
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e2200
          | exact resolve b2e2200 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2200
        have b2e2202 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e2201
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e2201
          | exact resolve b2e2201 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e2201
        have b2e2203 : False := by grind
        exact b2e2203
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b3e31 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b3e12 X0 x X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X1 X0) X2 X0
             have i₂ := b3e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e31 X0 X1 X2
             have i₂ := b3e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b3e31 X0 X1 X2
             have i₂ := b3e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b3e12 b3e31
          | exact resolve b3e31 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e56
        have b3e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e58
          | exact resolve b3e58 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e57 (σ X0)
             grind)
          | exact superpose b3e57 b3e18
          | exact resolve b3e18 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e63 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e63
          | exact resolve b3e63 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e85 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e23
          | exact resolve b3e23 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23
        have b3e88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b3e15 (σ x) (σ x)
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e15
          | exact resolve b3e15 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e90 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
        clear b3e88
        have b3e91 : (σ (k x y)) = (σ (k x x)) := by
          first
          | (have i₁ := b3e90
             have i₂ := b3e18 x x
             grind)
          | exact superpose b3e18 b3e90
          | exact resolve b3e90 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e93 : (σ (k x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e91
             have i₂ := b3e57 x
             grind)
          | exact superpose b3e57 b3e91
          | exact resolve b3e91 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e91
        have b3e192 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e93
             grind)
          | exact superpose b3e93 b3e85
          | exact resolve b3e85 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e196 : (k x y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e93
             grind)
          | exact superpose b3e93 b3e13
          | exact resolve b3e13 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e197 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b3e196
             have i₂ := b3e13 (M.op x x)
             grind)
          | exact superpose b3e13 b3e196
          | exact resolve b3e196 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e196
        have b3e209 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e32 (σ y) (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e32
          | exact resolve b3e32 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e210 : ∀ X0 : G, (M.op (σ (k x y)) (σ (k x y))) = (M.op X0 (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e32 (σ x) (σ x) x
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e32
          | exact resolve b3e32 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e262 : ∀ X0 : G, (M.op (σ (M.op x x)) (σ (M.op x x))) = (M.op X0 (σ (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e210 X0
             have i₂ := b3e93
             grind)
          | exact superpose b3e93 b3e210
          | exact resolve b3e210 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e210
        have b3e263 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (σ (k x y)) (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e209 X0
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e209
          | exact resolve b3e209 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e209
        have b3e265 : ∀ X0 : G, (M.op X0 (σ (M.op x x))) = (σ (M.op (M.op x x) (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e262 X0
             have i₂ := b3e70 (M.op x x)
             grind)
          | exact superpose b3e70 b3e262
          | exact resolve b3e262 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e262
        have b3e266 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (σ (M.op (k x y) (k x y))) := by
          intro X0
          first
          | (have i₁ := b3e263 X0
             have i₂ := b3e70 (k x y)
             grind)
          | exact superpose b3e70 b3e263
          | exact resolve b3e263 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e263
        have b3e267 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (σ (M.op (M.op x x) (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b3e266 X0
             have i₂ := b3e197
             grind)
          | exact superpose b3e197 b3e266
          | exact resolve b3e266 b3e197
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197 b3e266
        have b3e268 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b3e267 X0
             have i₂ := b3e70 y
             grind)
          | exact superpose b3e70 b3e267
          | exact resolve b3e267 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e267
        have b3e269 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x x))) = (M.op X0 (σ (M.op x y))) := by
          intro X0
          first
          | (have i₁ := b3e268 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e268
          | exact resolve b3e268 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e268
        have b3e435 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ x))) (M.op (σ y) (σ y)))) := by
          intro X0
          first
          | (have i₁ := b3e33 (σ y) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e33
          | exact resolve b3e33 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e451 : ∀ X0 X1 : G, (σ (k x y)) = (M.op X0 (M.op (M.op (σ x) (M.op X1 (σ x))) (σ (k x y)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e33 (σ x) X1 x
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e33
          | exact resolve b3e33 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e60
        have b3e489 : ∀ X0 X1 : G, (σ (M.op x x)) = (M.op X0 (M.op (M.op (σ x) (M.op X1 (σ x))) (σ (M.op x x)))) := by
          intro X0 X1
          first
          | (have i₁ := b3e451 X0 X1
             have i₂ := b3e93
             grind)
          | exact superpose b3e93 b3e451
          | exact resolve b3e451 b3e93
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e93 b3e451
        have b3e498 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ x))) (σ (M.op y y)))) := by
          intro X0
          first
          | (have i₁ := b3e435 X0
             have i₂ := b3e70 y
             grind)
          | exact superpose b3e70 b3e435
          | exact resolve b3e435 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e435
        have b3e507 : ∀ X0 : G, (σ (M.op x x)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b3e489 X0 x
             have i₂ := b3e265 (M.op (σ x) (M.op x (σ x)))
             grind)
          | exact superpose b3e265 b3e489
          | exact resolve b3e489 b3e265
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e265 b3e489
        have b3e510 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (M.op (σ y) (M.op (σ x) (σ x))) (σ (M.op x y)))) := by
          intro X0
          first
          | (have i₁ := b3e498 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e498
          | exact resolve b3e498 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e498
        have b3e513 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b3e510 X0
             have i₂ := b3e269 (M.op (σ y) (M.op (σ x) (σ x)))
             grind)
          | exact superpose b3e269 b3e510
          | exact resolve b3e510 b3e269
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e269 b3e510
        have b3e515 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e513 x
             have i₂ := b3e507 x
             grind)
          | exact superpose b3e507 b3e513
          | exact resolve b3e513 b3e507
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e507 b3e513
        have b3e516 : False := by grind
        exact b3e516
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e71 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e71
          have b4e75 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e73
            | exact resolve b4e73 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e77 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e75
            | exact resolve b4e75 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e75
          have b4e78 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e77
            | exact resolve b4e77 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e79 : False := by grind
          exact b4e79
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e68 (σ X0)
               grind)
            | exact superpose b5e68 b5e19
            | exact resolve b5e19 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e72 X0
               have i₂ := b5e68 X0
               grind)
            | exact superpose b5e68 b5e72
            | exact resolve b5e72 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e72
          have b5e90 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e94 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
            intro X0
            first
            | (have j0 := b5e90 X0
               have j1 := b5e16 X0 y
               grind)
            | (have r₁ := b5e90 X0
               have r₂ := b5e16 X0 y
               grind)
            | (have r₁ := b5e90 y
               have r₂ := b5e16 y y
               grind)
            | exact resolve b5e90 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e131 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 X0
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e16 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e16 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e16 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e16 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e16 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e140 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e150 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e131 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e131
          have b5e159 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e132 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e132 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e132 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e132 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e160 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e150 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e150 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | (have r₁ := b5e150 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e150 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e150
          have b5e166 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e160 X0 X1
               have j1 := b5e159 X0 X1
               grind)
            | (have r₁ := b5e160 X0 X1
               have r₂ := b5e159 X0 X1
               grind)
            | (have r₁ := b5e160 X1 X0
               have r₂ := b5e159 X0 X1
               grind)
            | exact resolve b5e160 b5e159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e159 b5e160
          have b5e435 : (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e94 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e94
          have b5e495 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e166 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e166
          have b5e2494 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e140 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e140
          have b5e2495 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b5e495 (σ x) (σ y)
               grind)
            | (have r₁ := b5e2494
               have r₂ := b5e495 (σ x) (σ y)
               grind)
            | exact resolve b5e2494 b5e495
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e495 b5e2494
          have b5e2496 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2495
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2495
            | exact resolve b5e2495 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2495
          have b5e2497 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2496
               have i₂ := b5e435
               grind)
            | exact superpose b5e435 b5e2496
            | exact resolve b5e2496 b5e435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e435 b5e2496
          have b5e2500 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2497
               grind)
            | exact superpose b5e2497 b5e23
            | exact resolve b5e23 b5e2497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2497
          have b5e2516 : False := by grind
          exact b5e2516
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e77 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e23
          | exact resolve b6e23 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e55
        have b6e146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e77
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e77 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e147 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e146
        have b6e148 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e147
             have r₂ := b6e20
             grind)
          | exact resolve b6e147 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e147
        have b6e149 : False := by grind
        exact b6e149
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e67
          have b7e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e69
            | exact resolve b7e69 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e71 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e68 y
               grind)
            | exact superpose b7e68 b7e70
            | exact resolve b7e70 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e68 (σ X0)
               grind)
            | exact superpose b7e68 b7e19
            | exact resolve b7e19 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e73 X0
               have i₂ := b7e68 X0
               grind)
            | exact superpose b7e68 b7e73
            | exact resolve b7e73 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e73
          have b7e92 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e94 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b7e92 X0
               have j1 := b7e16 X0 (σ y)
               grind)
            | (have r₁ := b7e92 X0
               have r₂ := b7e16 X0 (σ y)
               grind)
            | (have r₁ := b7e92 (σ y)
               have r₂ := b7e16 (σ y) (σ y)
               grind)
            | exact resolve b7e92 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e97 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e94 X0
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e94
            | (have j0 := b7e94 X0
               grind)
            | exact resolve b7e94 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e540 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e97 (σ x)
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e97
            | (have j0 := b7e97 (σ x)
               grind)
            | (have r₁ := b7e97 (σ x)
               have r₂ := b7e71
               grind)
            | exact resolve b7e97 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e97
          have b7e543 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e540
          have b7e545 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e543
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e543
            | exact resolve b7e543 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e543
          have b7e550 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e545
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e545
            | exact resolve b7e545 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e545
          have b7e567 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e550
               grind)
            | exact superpose b7e550 b7e14
            | exact resolve b7e14 b7e550
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e550
          have b7e568 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e567
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e567
            | exact resolve b7e567 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e567
          have b7e603 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e568
               grind)
            | exact superpose b7e568 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e568
          have b7e604 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b7e603
          have b7e606 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e604
               have r₂ := b7e21
               grind)
            | exact resolve b7e604 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e604
          have b7e609 : False := by grind
          exact b7e609
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e122 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e18 X1 X0
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
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e16
            | (have j0 := b8e16 X1 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e16 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e131 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e141 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e122 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e150 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               have j1 := b8e16 X1 X0
               grind)
            | (have r₁ := b8e123 X1 X0
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | exact resolve b8e123 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e151 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e141 X0 X1
               have j1 := b8e16 X1 X0
               grind)
            | (have r₁ := b8e141 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | (have r₁ := b8e141 X1 X0
               have r₂ := b8e16 X0 X1
               grind)
            | exact resolve b8e141 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e141
          have b8e157 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e151 X0 X1
               have j1 := b8e150 X0 X1
               grind)
            | (have r₁ := b8e151 X0 X1
               have r₂ := b8e150 X0 X1
               grind)
            | (have r₁ := b8e151 X1 X0
               have r₂ := b8e150 X0 X1
               grind)
            | exact resolve b8e151 b8e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e150 b8e151
          have b8e409 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e157 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157
          have b8e2157 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e2158 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j1 := b8e409 (σ x) (σ y)
               grind)
            | (have r₁ := b8e2157
               have r₂ := b8e409 (σ x) (σ y)
               grind)
            | exact resolve b8e2157 b8e409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e409 b8e2157
          have b8e2159 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e2158
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e2158
            | exact resolve b8e2158 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2158
          have b8e2164 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2159
               grind)
            | exact superpose b8e2159 b8e20
            | exact resolve b8e20 b8e2159
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2159
          have b8e2228 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e2164
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2164
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e2164 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2164
          have b8e2229 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e2228
          have b8e2232 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e2229
               have r₂ := b8e21
               grind)
            | exact resolve b8e2229 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2229
          have b8e2233 : False := by grind
          exact b8e2233

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxy_pxx_pxy_Equation3274 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
      have b0e43 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x x
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ x)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e45
      have b0e48 : (M.op x x) = (k x y) := by grind
      clear b0e43
      have b0e49 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e47
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e47
        | exact resolve b0e47 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e47
      have b0e50 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e49
        | exact resolve b0e49 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e49
      have b0e51 : False := by grind
      exact b0e51
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
        have b1e26 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y (M.op x x))) := by
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
        have b1e27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X1 X0) X2 X0
             have i₂ := b1e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e56 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e56
        have b1e60 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e61 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e60
          | exact resolve b1e60 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e57 (σ X0)
             grind)
          | exact superpose b1e57 b1e18
          | exact resolve b1e18 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e63 X0
             have i₂ := b1e57 X0
             grind)
          | exact superpose b1e57 b1e63
          | exact resolve b1e63 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e63
        have b1e161 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e23
          | exact resolve b1e23 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e172 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b1e12 (M.op x x) X0 y
             have i₂ := b1e26 (M.op x x)
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e195 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
          intro X0
          first
          | (have i₁ := b1e28 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e28
          | exact resolve b1e28 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e247 : ∀ X0 : G, (M.op (σ (M.op y y)) (σ (M.op y y))) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b1e195 X0
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e195
          | exact resolve b1e195 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e195
        have b1e252 : ∀ X0 : G, (σ (M.op (M.op y y) (M.op y y))) = (M.op X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b1e247 X0
             have i₂ := b1e70 (M.op y y)
             grind)
          | exact superpose b1e70 b1e247
          | exact resolve b1e247 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e247
        have b1e254 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = (σ (M.op (M.op x x) (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b1e252 X0
             have i₂ := b1e172 (M.op y y)
             grind)
          | exact superpose b1e172 b1e252
          | exact resolve b1e252 b1e172
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e172 b1e252
        have b1e302 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e28 (σ X0) (σ X0) x
             have i₂ := b1e70 X0
             grind)
          | exact superpose b1e70 b1e28
          | exact resolve b1e28 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e315 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
          intro X0 X1
          first
          | (have i₁ := b1e302 X0 X1
             have i₂ := b1e70 (M.op X0 X0)
             grind)
          | exact superpose b1e70 b1e302
          | exact resolve b1e302 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e302
        have b1e517 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) (M.op (σ x) (σ y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e29 (σ y) X1 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e29
          | exact resolve b1e29 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e518 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op (M.op (σ X0) (M.op X2 (σ X0))) (σ (M.op X0 X0)))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 (σ X0) X1 X2
             have i₂ := b1e70 X0
             grind)
          | exact superpose b1e70 b1e29
          | exact resolve b1e29 b1e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e70
        have b1e551 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e518 X0 X1 x
             have i₂ := b1e315 X0 (M.op (σ X0) (M.op x (σ X0)))
             grind)
          | exact superpose b1e315 b1e518
          | exact resolve b1e518 b1e315
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e315 b1e518
        have b1e552 : ∀ X0 X1 : G, (σ (M.op y y)) = (M.op X0 (M.op (M.op (σ y) (M.op X1 (σ y))) (σ (M.op y y)))) := by
          intro X0 X1
          first
          | (have i₁ := b1e517 X0 X1
             have i₂ := b1e61
             grind)
          | exact superpose b1e61 b1e517
          | exact resolve b1e517 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e517
        have b1e569 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (σ (M.op (M.op x x) (M.op x x)))) := by
          intro X0
          first
          | (have i₁ := b1e552 X0 x
             have i₂ := b1e254 (M.op (σ y) (M.op x (σ y)))
             grind)
          | exact superpose b1e254 b1e552
          | exact resolve b1e552 b1e254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e254 b1e552
        have b1e572 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e569 x
             have i₂ := b1e551 x x
             grind)
          | exact superpose b1e551 b1e569
          | exact resolve b1e569 b1e551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e551 b1e569
        have b1e575 : False := by grind
        exact b1e575
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e54 : (M.op x x) = (k x y) := by grind
        clear b2e51
        have b2e98 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e124 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b2e98 X0
             have j1 := b2e15 X0 (σ y)
             grind)
          | (have r₁ := b2e98 X0
             have r₂ := b2e15 X0 (σ y)
             grind)
          | (have r₁ := b2e98 (σ y)
             have r₂ := b2e15 (σ y) (σ y)
             grind)
          | exact resolve b2e98 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e98
        have b2e909 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e124 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e124
        have b2e910 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e909
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e909
          | exact resolve b2e909 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e909
        have b2e911 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e910
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e910
          | exact resolve b2e910 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e910
        have b2e912 : False := by grind
        exact b2e912
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b3e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X1 X0) X2 X0
             have i₂ := b3e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e57 (σ X0)
             grind)
          | exact superpose b3e57 b3e18
          | exact resolve b3e18 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e70 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e63 X0
             have i₂ := b3e57 X0
             grind)
          | exact superpose b3e57 b3e63
          | exact resolve b3e63 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e63
        have b3e203 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 X1
             have i₂ := b3e32 X1 X0 X1
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e550 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e32 (M.op (σ x) (σ x)) (σ y) X0
             have i₂ := b3e43 (M.op (σ y) (M.op (σ x) (σ x)))
             grind)
          | exact superpose b3e43 b3e32
          | exact resolve b3e32 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e43
        have b3e583 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e550 x
             have i₂ := b3e203 (σ x) (σ x) x
             grind)
          | exact superpose b3e203 b3e550
          | exact resolve b3e550 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e203 b3e550
        have b3e605 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e583
             have i₂ := b3e70 y
             grind)
          | exact superpose b3e70 b3e583
          | exact resolve b3e583 b3e70
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e70 b3e583
        have b3e625 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e605
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e605
          | exact resolve b3e605 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e605
        have b3e641 : False := by grind
        exact b3e641
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e71 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e71
          have b4e75 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e73
            | exact resolve b4e73 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e77 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e75
            | exact resolve b4e75 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e75
          have b4e78 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e77
            | exact resolve b4e77 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e79 : False := by grind
          exact b4e79
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e68 (σ X0)
               grind)
            | exact superpose b5e68 b5e19
            | exact resolve b5e19 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e72 X0
               have i₂ := b5e68 X0
               grind)
            | exact superpose b5e68 b5e72
            | exact resolve b5e72 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e72
          have b5e90 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X1 X1
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X1 X0
               have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e137 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e145 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e147 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e128 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e150 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e145 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e145 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e145 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e145 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e145
          have b5e155 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e137 X0
               have j1 := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e137 X0
               have r₂ := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e137 (σ y)
               have r₂ := b5e16 (σ y) (σ y)
               grind)
            | exact resolve b5e137 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e137
          have b5e161 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e147 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e147 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | (have r₁ := b5e147 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e147 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e147
          have b5e177 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e161 X0 X1
               have j1 := b5e150 X1 X0
               grind)
            | (have r₁ := b5e161 X0 X1
               have r₂ := b5e150 X0 X1
               grind)
            | (have r₁ := b5e161 X1 X0
               have r₂ := b5e150 X0 X1
               grind)
            | exact resolve b5e161 b5e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e150 b5e161
          have b5e573 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e177 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e177
          have b5e1127 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e155 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e155
          have b5e1128 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1127
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1127
            | exact resolve b5e1127 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1127
          have b5e1220 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e90 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e1221 : (M.op x x) = (k x y) := by
            first
            | (have j1 := b5e573 x y
               grind)
            | (have r₁ := b5e1220
               have r₂ := b5e573 x y
               grind)
            | exact resolve b5e1220 b5e573
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e573 b5e1220
          have b5e2067 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1128
               grind)
            | exact superpose b5e1128 b5e23
            | exact resolve b5e23 b5e1128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1128
          have b5e2086 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2067
               have i₂ := b5e1221
               grind)
            | exact superpose b5e1221 b5e2067
            | exact resolve b5e2067 b5e1221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1221 b5e2067
          have b5e2092 : False := by grind
          exact b5e2092
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e54 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e76 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e23
          | exact resolve b6e23 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e55
        have b6e159 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e76
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e76
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e76 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e160 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e159
        have b6e161 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e160
             have r₂ := b6e20
             grind)
          | exact resolve b6e160 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160
        have b6e162 : False := by grind
        exact b6e162
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e67
          have b7e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e69
            | exact resolve b7e69 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e71 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e68 y
               grind)
            | exact superpose b7e68 b7e70
            | exact resolve b7e70 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e68 (σ X0)
               grind)
            | exact superpose b7e68 b7e19
            | exact resolve b7e19 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e73 X0
               have i₂ := b7e68 X0
               grind)
            | exact superpose b7e68 b7e73
            | exact resolve b7e73 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e73
          have b7e92 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e94 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e92 X0
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e92
            | (have j0 := b7e92 X0
               grind)
            | exact resolve b7e92 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e98 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e23
            | exact resolve b7e23 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e104 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e98
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e98
            | exact resolve b7e98 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e98
          have b7e134 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X1 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X1 X1 X1
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e153 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b7e134 X0 X1 X2
               have j1 := b7e16 X0 X1
               grind)
            | (have r₁ := b7e134 X0 X0 X0
               have r₂ := b7e16 X0 (M.op X0 (M.op X0 X0))
               grind)
            | (have r₁ := b7e134 X0 X1 X2
               have r₂ := b7e16 X0 X1
               grind)
            | (have r₁ := b7e134 X1 X1 X2
               have r₂ := b7e16 X1 X1
               grind)
            | exact resolve b7e134 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e134
          have b7e173 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e153 X0 X1 x
               have i₂ := b7e13 X1 x X0
               grind)
            | (have i₁ := b7e153 X0 X1 (M.op X1 (M.op X0 X1))
               have i₂ := b7e13 (M.op X1 (M.op X0 X1)) X1 x
               grind)
            | exact superpose b7e13 b7e153
            | (have j0 := b7e153 X0 X1 x
               grind)
            | exact resolve b7e153 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e153
          have b7e2209 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e94 (σ x)
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e94
            | (have j0 := b7e94 (σ x)
               grind)
            | (have r₁ := b7e94 (σ x)
               have r₂ := b7e71
               grind)
            | exact resolve b7e94 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71 b7e94
          have b7e2210 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e2209
          have b7e2212 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e2210
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e2210
            | exact resolve b7e2210 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2210
          have b7e2214 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e2212
               have r₂ := b7e104
               grind)
            | exact resolve b7e2212 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104 b7e2212
          have b7e2215 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e2214
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e2214
            | exact resolve b7e2214 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2214
          have b7e2216 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e2215
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e2215
            | exact resolve b7e2215 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e2215
          have b7e2228 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e2216
               grind)
            | exact superpose b7e2216 b7e14
            | exact resolve b7e14 b7e2216
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2216
          have b7e2229 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e2228
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e2228
            | exact resolve b7e2228 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2228
          have b7e2447 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e173 x y
               have i₂ := b7e2229
               grind)
            | exact superpose b7e2229 b7e173
            | (have j0 := b7e173 x y
               grind)
            | exact resolve b7e173 b7e2229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e173 b7e2229
          have b7e2454 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e2447
               have r₂ := b7e21
               grind)
            | exact resolve b7e2447 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2447
          have b7e2462 : False := by grind
          exact b7e2462
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
            intro X0 X1 X2
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e127 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X1 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e129 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e147 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e129 X0
               have j1 := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e129 X0
               have r₂ := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e129 (σ y)
               have r₂ := b8e16 (σ y) (σ y)
               grind)
            | exact resolve b8e129 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e148 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have j0 := b8e127 X0 X1 X2
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e127 X0 X0 X0
               have r₂ := b8e16 X0 (M.op X0 (M.op X0 X0))
               grind)
            | (have r₁ := b8e127 X0 X1 X2
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e127 X1 X1 X2
               have r₂ := b8e16 X1 X1
               grind)
            | exact resolve b8e127 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e127
          have b8e167 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e148 X0 X1 x
               have i₂ := b8e13 X1 x X0
               grind)
            | (have i₁ := b8e148 X0 X1 (M.op X1 (M.op X0 X1))
               have i₂ := b8e13 (M.op X1 (M.op X0 X1)) X1 x
               grind)
            | exact superpose b8e13 b8e148
            | (have j0 := b8e148 X0 X1 x
               grind)
            | exact resolve b8e148 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e148
          have b8e927 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e147 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e928 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e927
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e927
            | exact resolve b8e927 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e927
          have b8e1315 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e928
               grind)
            | exact superpose b8e928 b8e20
            | exact resolve b8e20 b8e928
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e928
          have b8e1397 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1315
               have i₂ := b8e167 x y
               grind)
            | exact superpose b8e167 b8e1315
            | (have j1 := b8e167 x y
               grind)
            | exact resolve b8e1315 b8e167
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167 b8e1315
          have b8e1400 : (M.op x y) = (M.op y y) := by grind
          clear b8e1397
          have b8e1404 : False := by grind
          exact b8e1404

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3274 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
      have b0e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e53 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e53
        | exact resolve b0e53 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e53
      have b0e312 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e58 x
           grind)
        | exact superpose b0e58 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e58 x
           grind)
        | exact resolve b0e22 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e58
      have b0e324 : False := by grind
      exact b0e324
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
        have b1e26 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y (M.op x x))) := by
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
        have b1e27 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X0 (M.op X1 X0)) X2 x
             have i₂ := b1e12 X0 x X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 (M.op X1 X0) X2 X0
             have i₂ := b1e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 X0 (M.op X0 (M.op X1 X0)) X1
             grind)
          | (have i₁ := b1e27 X0 X1 X2
             have i₂ := b1e12 (M.op X0 (M.op X1 X0)) X1 X2
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e56 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e56
        have b1e60 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e58
          | exact resolve b1e58 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58
        have b1e62 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e57 y
             grind)
          | exact superpose b1e57 b1e60
          | exact resolve b1e60 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e60
        have b1e144 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e62
             grind)
          | exact superpose b1e62 b1e23
          | exact resolve b1e23 b1e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e62
        have b1e183 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b1e28 X1 x X3
             have i₂ := b1e28 X1 x X0
             grind)
          | (have i₁ := b1e28 X0 X0 x
             have i₂ := b1e28 X0 X1 (M.op X0 X0)
             grind)
          | exact superpose b1e28 b1e28
          | exact resolve b1e28 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e645 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e29 X1 x X2
             have i₂ := b1e183 (M.op X1 (M.op x X1)) X1 X0
             grind)
          | (have i₁ := b1e29 X1 x X2
             have i₂ := b1e183 X0 X1 (M.op X1 (M.op x X1))
             grind)
          | exact superpose b1e183 b1e29
          | exact resolve b1e29 b1e183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29 b1e183
        have b1e905 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e26 x
             have i₂ := b1e645 y x x
             grind)
          | exact superpose b1e645 b1e26
          | exact resolve b1e26 b1e645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e645
        have b1e1093 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e144
             have i₂ := b1e905
             grind)
          | exact superpose b1e905 b1e144
          | exact resolve b1e144 b1e905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e144 b1e905
        have b1e1113 : False := by grind
        exact b1e1113
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e51 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : (M.op y y) = (k x y) := by grind
        clear b2e51
        have b2e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e53 (σ X0)
             grind)
          | exact superpose b2e53 b2e18
          | exact resolve b2e18 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e57 X0
             have i₂ := b2e53 X0
             grind)
          | exact superpose b2e53 b2e57
          | exact resolve b2e57 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e57
        have b2e99 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e172 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e64 y
             grind)
          | exact superpose b2e64 b2e22
          | exact resolve b2e22 b2e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e64
        have b2e1661 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e1662 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1661
             have r₂ := b2e21
             grind)
          | exact resolve b2e1661 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1661
        have b2e1663 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1662
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1662
          | exact resolve b2e1662 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1662
        have b2e1664 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1663
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e1663
          | exact resolve b2e1663 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e1663
        have b2e1665 : False := by grind
        exact b2e1665
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b3e32 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 (M.op X1 X0) X2 X0
             have i₂ := b3e12 X0 (M.op X1 X0) X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) X0 (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e58 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e56
        have b3e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e58
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e58
          | exact resolve b3e58 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e86 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e15
          | exact resolve b3e15 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e88 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e86
        have b3e89 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e88
          | exact resolve b3e88 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88
        have b3e90 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e89
             have i₂ := b3e57 y
             grind)
          | exact superpose b3e57 b3e89
          | exact resolve b3e89 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e89
        have b3e91 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e90
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e90
          | exact resolve b3e90 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90
        have b3e191 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 X1
             have i₂ := b3e32 X1 X0 X1
             grind)
          | exact superpose b3e32 b3e12
          | exact resolve b3e12 b3e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e339 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e32 (M.op (σ x) (σ x)) (σ y) X0
             have i₂ := b3e43 (M.op (σ y) (M.op (σ x) (σ x)))
             grind)
          | exact superpose b3e43 b3e32
          | exact resolve b3e32 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32 b3e43
        have b3e365 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e339 x
             have i₂ := b3e191 (σ x) (σ x) x
             grind)
          | exact superpose b3e191 b3e339
          | exact resolve b3e339 b3e191
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e191 b3e339
        have b3e382 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e365
             have i₂ := b3e60
             grind)
          | exact superpose b3e60 b3e365
          | exact resolve b3e365 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e365
        have b3e398 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e382
             have i₂ := b3e91
             grind)
          | exact superpose b3e91 b3e382
          | exact resolve b3e382 b3e91
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91 b3e382
        have b3e410 : False := by grind
        exact b3e410
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : (M.op x y) = (M.op y y) := by grind
          have b4e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e71 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e71
          have b4e75 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e73
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e73
            | exact resolve b4e73 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73
          have b4e78 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e72 y
               grind)
            | exact superpose b4e72 b4e75
            | exact resolve b4e75 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e75
          have b4e79 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e78
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e78
            | exact resolve b4e78 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e80 : False := by grind
          exact b4e80
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e68 (σ X0)
               grind)
            | exact superpose b5e68 b5e19
            | exact resolve b5e19 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e73 X0
               have i₂ := b5e68 X0
               grind)
            | exact superpose b5e68 b5e73
            | exact resolve b5e73 b5e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e68 b5e73
          have b5e91 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e138 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e619 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e91 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91
          have b5e620 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e619
               have r₂ := b5e21
               grind)
            | exact resolve b5e619 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e619
          have b5e2097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e138 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e138
          have b5e2098 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e2097
               have r₂ := b5e23
               grind)
            | exact resolve b5e2097 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2097
          have b5e2099 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e2098
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e2098
            | exact resolve b5e2098 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2098
          have b5e2100 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e2099
               have i₂ := b5e620
               grind)
            | exact superpose b5e620 b5e2099
            | exact resolve b5e2099 b5e620
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e620 b5e2099
          have b5e2103 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2100
               grind)
            | exact superpose b5e2100 b5e23
            | exact resolve b5e23 b5e2100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2100
          have b5e2125 : False := by grind
          exact b5e2125
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e52
        have b6e55 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e54
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e54
          | exact resolve b6e54 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e79 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e55
             grind)
          | exact superpose b6e55 b6e15
          | exact resolve b6e15 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e81 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e79
        have b6e82 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e81
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e81
          | exact resolve b6e81 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81
        have b6e83 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e82
             have i₂ := b6e53 y
             grind)
          | exact superpose b6e53 b6e82
          | exact resolve b6e82 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e82
        have b6e144 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e83
             grind)
          | exact superpose b6e83 b6e13
          | exact resolve b6e13 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e145 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e144
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e144
          | exact resolve b6e144 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e212 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e145
             grind)
          | exact superpose b6e145 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e213 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e212
        have b6e215 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e213
             have r₂ := b6e21
             grind)
          | exact resolve b6e213 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e213
        have b6e217 : False := by grind
        exact b6e217
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e67 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e67
          have b7e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e69
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e69
            | exact resolve b7e69 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e69
          have b7e72 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e68 y
               grind)
            | exact superpose b7e68 b7e70
            | exact resolve b7e70 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e68 (σ X0)
               grind)
            | exact superpose b7e68 b7e19
            | exact resolve b7e19 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e74 X0
               have i₂ := b7e68 X0
               grind)
            | exact superpose b7e68 b7e74
            | exact resolve b7e74 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e74
          have b7e93 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e95 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e93 X0
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e93
            | (have j0 := b7e93 X0
               grind)
            | exact resolve b7e93 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e99 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e23
            | exact resolve b7e23 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e105 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e99
               have i₂ := b7e83 x
               grind)
            | exact superpose b7e83 b7e99
            | exact resolve b7e99 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e99
          have b7e1216 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e95 (σ x)
               have i₂ := b7e72
               grind)
            | exact superpose b7e72 b7e95
            | (have j0 := b7e95 (σ x)
               grind)
            | (have r₁ := b7e95 (σ x)
               have r₂ := b7e72
               grind)
            | exact resolve b7e95 b7e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72 b7e95
          have b7e1217 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e1216
          have b7e1218 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1217
               have i₂ := b7e83 x
               grind)
            | exact superpose b7e83 b7e1217
            | exact resolve b7e1217 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1217
          have b7e1219 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e1218
               have r₂ := b7e105
               grind)
            | exact resolve b7e1218 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e1218
          have b7e1220 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1219
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1219
            | exact resolve b7e1219 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1219
          have b7e1221 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1220
               have i₂ := b7e83 x
               grind)
            | exact superpose b7e83 b7e1220
            | exact resolve b7e1220 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83 b7e1220
          have b7e1230 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1221
               grind)
            | exact superpose b7e1221 b7e14
            | exact resolve b7e14 b7e1221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1221
          have b7e1231 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1230
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e1230
            | exact resolve b7e1230 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1230
          have b7e1403 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e1231
               grind)
            | exact superpose b7e1231 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e1231
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1231
          have b7e1404 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b7e1403
          have b7e1407 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e1404
               have r₂ := b7e21
               grind)
            | exact resolve b7e1404 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1404
          have b7e1411 : False := by grind
          exact b7e1411
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e130 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1941 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e130 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e1942 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1941
               have r₂ := b8e23
               grind)
            | exact resolve b8e1941 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1941
          have b8e1943 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1942
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1942
            | exact resolve b8e1942 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1942
          have b8e1948 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1943
               grind)
            | exact superpose b8e1943 b8e20
            | exact resolve b8e20 b8e1943
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1943
          have b8e2026 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1948
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1948
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1948 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1948
          have b8e2027 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e2026
          have b8e2029 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e2027
               have r₂ := b8e21
               grind)
            | exact resolve b8e2027 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2027
          have b8e2031 : False := by grind
          exact b8e2031

/-- `Equation3274`: `x ◇ x = y ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_pyy_pxx_pxy_Equation3274 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3274 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3274.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (M.op y y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b0e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : (M.op x y) = (M.op y y) := by grind
      have b0e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e19 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e16
        | exact resolve b0e16 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e20 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e19
        | exact resolve b0e19 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19
      have b0e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e44 (σ X0)
           grind)
        | exact superpose b0e44 b0e15
        | exact resolve b0e15 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e44 X0
           grind)
        | exact superpose b0e44 b0e52
        | exact resolve b0e52 b0e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44 b0e52
      have b0e419 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e57 y
           grind)
        | exact superpose b0e57 b0e20
        | (have r₁ := b0e20
           have r₂ := b0e57 y
           grind)
        | exact resolve b0e20 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e57
      have b0e435 : False := by grind
      exact b0e435
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b1e17 : (M.op x y) = (M.op y y) := by grind
      have b1e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b1e16
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e16
        | exact resolve b1e16 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op X0 (M.op X1 X0)) X2 x
           have i₂ := b1e10 X0 x X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op X1 X0) X2 X0
           have i₂ := b1e10 X0 (M.op X1 X0) X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e25 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e23 X0 X1 X2
           have i₂ := b1e10 X0 (M.op X0 (M.op X1 X0)) X1
           grind)
        | (have i₁ := b1e23 X0 X1 X2
           have i₂ := b1e10 (M.op X0 (M.op X1 X0)) X1 X2
           grind)
        | exact superpose b1e10 b1e23
        | exact resolve b1e23 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e23
      have b1e38 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
        first
        | (have i₁ := b1e13 x y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 y y
           grind)
        | (have r₁ := b1e13 x y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e42 : (M.op x x) = (k x y) := by grind
      clear b1e38
      have b1e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e41 (σ X0)
           grind)
        | exact superpose b1e41 b1e15
        | exact resolve b1e15 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e46 X0
           have i₂ := b1e41 X0
           grind)
        | exact superpose b1e41 b1e46
        | exact resolve b1e46 b1e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e41 b1e46
      have b1e66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 X0 X1
           have i₂ := b1e14 (σ X0) (σ X1)
           grind)
        | exact superpose b1e14 b1e15
        | (have j1 := b1e14 (σ X0) (σ X1)
           grind)
        | exact resolve b1e15 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e71 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e66 X0 X1
           have i₂ := b1e51 X1
           grind)
        | exact superpose b1e51 b1e66
        | (have j0 := b1e66 X0 X1
           grind)
        | exact resolve b1e66 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e66
      have b1e126 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X3 (M.op X1 X1)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b1e24 X1 x X3
           have i₂ := b1e24 X1 x X0
           grind)
        | (have i₁ := b1e24 X0 X0 x
           have i₂ := b1e24 X0 X1 (M.op X0 X0)
           grind)
        | exact superpose b1e24 b1e24
        | exact resolve b1e24 b1e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e408 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e71 x y
           grind)
        | exact superpose b1e71 b1e18
        | (have j1 := b1e71 x y
           grind)
        | exact resolve b1e18 b1e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e415 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op (σ X1) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) X2 (σ X0)
           have i₂ := b1e71 X0 X1
           grind)
        | exact superpose b1e71 b1e10
        | (have j1 := b1e71 X0 X1
           grind)
        | exact resolve b1e10 b1e71
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e71
      have b1e427 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op (σ X1) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e415 X0 X1 X2
           have i₂ := b1e51 X1
           grind)
        | exact superpose b1e51 b1e415
        | (have j0 := b1e415 X0 X1 X2
           grind)
        | exact resolve b1e415 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e415
      have b1e431 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e408
           have r₂ := b1e19
           grind)
        | exact resolve b1e408 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e408
      have b1e453 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e431
           have i₂ := b1e42
           grind)
        | exact superpose b1e42 b1e431
        | exact resolve b1e431 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e431
      have b1e458 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e453
           have i₂ := b1e51 y
           grind)
        | exact superpose b1e51 b1e453
        | exact resolve b1e453 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e453
      have b1e938 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 (M.op X1 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e25 X1 x X2
           have i₂ := b1e126 (M.op X1 (M.op x X1)) X1 X0
           grind)
        | (have i₁ := b1e25 X1 x X2
           have i₂ := b1e126 X0 X1 (M.op X1 (M.op x X1))
           grind)
        | exact superpose b1e126 b1e25
        | exact resolve b1e25 b1e126
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25 b1e126
      have b1e2470 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e938 X0 (σ X0) X2
           have i₂ := b1e51 X0
           grind)
        | exact superpose b1e51 b1e938
        | exact resolve b1e938 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51 b1e938
      have b1e55015 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e427 x y X0
           have i₂ := b1e42
           grind)
        | exact superpose b1e42 b1e427
        | (have j0 := b1e427 x y x
           grind)
        | exact resolve b1e427 b1e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e42 b1e427
      have b1e55441 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ y) (σ (M.op x x)))) := by
        intro X0
        first
        | (have j0 := b1e55015 X0
           grind)
        | (have r₁ := b1e55015 X0
           have r₂ := b1e19
           grind)
        | exact resolve b1e55015 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e55015
      have b1e55562 : (σ (M.op y y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e55441 x
           have i₂ := b1e2470 x x (σ y)
           grind)
        | exact superpose b1e2470 b1e55441
        | exact resolve b1e55441 b1e2470
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2470 b1e55441
      have b1e55652 : False := by grind
      exact b1e55652
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X2 X0))) := by
        intro X0 X1 X2
        grind
      have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b2e18 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e22 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X0 (M.op X1 X0)) X2 x
           have i₂ := b2e10 X0 x X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e23 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 (M.op X1 X0) X2 X0
           have i₂ := b2e10 X0 (M.op X1 X0) X1
           grind)
        | exact superpose b2e10 b2e10
        | exact resolve b2e10 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e22 X0 X1 X2
           have i₂ := b2e10 X0 (M.op X0 (M.op X1 X0)) X1
           grind)
        | (have i₁ := b2e22 X0 X1 X2
           have i₂ := b2e10 (M.op X0 (M.op X1 X0)) X1 X2
           grind)
        | exact superpose b2e10 b2e22
        | exact resolve b2e22 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e22
      have b2e39 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 (σ y) (σ y)
           grind)
        | (have r₁ := b2e13 (σ x) (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e42 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e39
      have b2e44 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e42
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e42
        | exact resolve b2e42 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e42
      have b2e78 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e44
           grind)
        | exact superpose b2e44 b2e13
        | exact resolve b2e13 b2e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e82 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e78
      have b2e83 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e82
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e82
        | exact resolve b2e82 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e82
      have b2e84 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e83
           have i₂ := b2e41 x
           grind)
        | exact superpose b2e41 b2e83
        | exact resolve b2e83 b2e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e41 b2e83
      have b2e112 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e84
           grind)
        | exact superpose b2e84 b2e11
        | exact resolve b2e11 b2e84
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e84
      have b2e113 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e112
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e112
        | exact resolve b2e112 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e112
      have b2e149 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op (M.op X0 X1) (M.op X0 X1))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b2e10 X1 X2 X1
           have i₂ := b2e23 X1 X0 X1
           grind)
        | exact superpose b2e23 b2e10
        | exact resolve b2e10 b2e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e168 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e113
           grind)
        | exact superpose b2e113 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e113
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e113
      have b2e169 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b2e168
           have r₂ := b2e17
           grind)
        | exact resolve b2e168 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e168
      have b2e217 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b2e23 x x x
           have i₂ := b2e169
           grind)
        | exact superpose b2e169 b2e23
        | exact resolve b2e23 b2e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e23
      have b2e247 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op (M.op x (M.op X1 x)) (M.op x y))) := by
        intro X0 X1
        first
        | (have i₁ := b2e24 x X1 x
           have i₂ := b2e169
           grind)
        | exact superpose b2e169 b2e24
        | exact resolve b2e24 b2e169
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24 b2e169
      have b2e268 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e247 X0 x
           have i₂ := b2e217 (M.op x (M.op x x))
           grind)
        | exact superpose b2e217 b2e247
        | exact resolve b2e247 b2e217
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e217 b2e247
      have b2e281 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e268 x
           have i₂ := b2e149 x y x
           grind)
        | exact superpose b2e149 b2e268
        | exact resolve b2e268 b2e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e149 b2e268
      have b2e287 : False := by grind
      exact b2e287
    · have b3e13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e17 : (M.op x y) ≠ (M.op y y) := by grind
      have b3e18 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e38 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e42 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e38 (σ X0)
           grind)
        | exact superpose b3e38 b3e15
        | exact resolve b3e15 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e47 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e42 X0
           have i₂ := b3e38 X0
           grind)
        | exact superpose b3e38 b3e42
        | exact resolve b3e42 b3e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e38 b3e42
      have b3e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X0 X1
           have i₂ := b3e14 (σ X0) (σ X1)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 (σ X0) (σ X1)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e67 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e62 X0 X1
           have i₂ := b3e47 X1
           grind)
        | exact superpose b3e47 b3e62
        | (have j0 := b3e62 X0 X1
           grind)
        | exact resolve b3e62 b3e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e62
      have b3e426 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e67 x y
           grind)
        | exact superpose b3e67 b3e16
        | (have j1 := b3e67 x y
           grind)
        | exact resolve b3e16 b3e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e67
      have b3e20631 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b3e426
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e426
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e426 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e426
      have b3e20637 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b3e20631
      have b3e20638 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have r₁ := b3e20637
           have r₂ := b3e17
           grind)
        | exact resolve b3e20637 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20637
      have b3e20643 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e20638
           grind)
        | exact superpose b3e20638 b3e18
        | exact resolve b3e18 b3e20638
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20638
      have b3e20700 : False := by grind
      exact b3e20700

/-- `Equation3279`: `x ◇ x = y ◇ (y ◇ (x ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_x_y_pyy_x_pxy_Equation3279 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3279 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3279.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : (M.op x y) = (M.op x x) := by grind
      have b0e20 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e23 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
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
      have b0e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e48 (σ X0)
           grind)
        | exact superpose b0e48 b0e17
        | exact resolve b0e17 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e55 X0
           have i₂ := b0e48 X0
           grind)
        | exact superpose b0e48 b0e55
        | exact resolve b0e55 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e55
      have b0e172 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e23
           have i₂ := b0e60 x
           grind)
        | exact superpose b0e60 b0e23
        | (have r₁ := b0e23
           have r₂ := b0e60 x
           grind)
        | exact resolve b0e23 b0e60
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23 b0e60
      have b0e180 : False := by grind
      exact b0e180
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e19
          | exact resolve b2e19 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e31 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X1 X0))) = (M.op X2 (M.op X2 (M.op X1 X2))) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e12 X1 X2
             have i₂ := b2e12 X1 X0
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e52 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : (k x y) = (M.op y y) := by grind
        clear b2e52
        have b2e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
        have b2e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e55 X0
             grind)
          | exact superpose b2e55 b2e59
          | exact resolve b2e59 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e59
        have b2e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
        have b2e88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e75 X0 X1
             have i₂ := b2e66 X0
             grind)
          | exact superpose b2e66 b2e75
          | (have j0 := b2e75 X0 X1
             grind)
          | exact resolve b2e75 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e75
        have b2e158 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b2e12 (σ X0) (σ X0)
             have i₂ := b2e66 X0
             grind)
          | exact superpose b2e66 b2e12
          | exact resolve b2e12 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1320 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e88 x y
             grind)
          | exact superpose b2e88 b2e21
          | (have j1 := b2e88 x y
             grind)
          | exact resolve b2e21 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1329 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op (σ X0) X2))) = (M.op (σ X1) (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e31 X2 (σ X0) (σ X1)
             have i₂ := b2e88 X0 X1
             grind)
          | exact superpose b2e88 b2e31
          | (have j1 := b2e88 X0 X1
             grind)
          | exact resolve b2e31 b2e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31 b2e88
        have b2e1404 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e1320
             have r₂ := b2e24
             grind)
          | exact resolve b2e1320 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1320
        have b2e1435 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e1404
             have r₂ := b2e22
             grind)
          | exact resolve b2e1404 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1404
        have b2e1455 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1435
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e1435
          | exact resolve b2e1435 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1435
        have b2e1466 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1455
             have i₂ := b2e66 x
             grind)
          | exact superpose b2e66 b2e1455
          | exact resolve b2e1455 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1455
        have b2e69994 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) X0))) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b2e1329 x y X0
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e1329
          | (have j0 := b2e1329 x y x
             grind)
          | exact resolve b2e1329 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e1329
        have b2e70582 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) X0))) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have j0 := b2e69994 X0
             grind)
          | (have r₁ := b2e69994 X0
             have r₂ := b2e24
             grind)
          | exact resolve b2e69994 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e69994
        have b2e70604 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) X0))) = (M.op (σ y) (M.op (σ y) (σ (M.op y y)))) := by
          intro X0
          first
          | (have j0 := b2e70582 X0
             grind)
          | (have r₁ := b2e70582 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e70582 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70582
        have b2e70612 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op (σ x) X0))) = (σ (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b2e70604 X0
             have i₂ := b2e158 y
             grind)
          | exact superpose b2e158 b2e70604
          | exact resolve b2e70604 b2e158
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e158 b2e70604
        have b2e70616 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e70612 x
             have i₂ := b2e12 (σ x) x
             grind)
          | exact superpose b2e12 b2e70612
          | exact resolve b2e70612 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e70612
        have b2e70617 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e70616
             have i₂ := b2e66 x
             grind)
          | exact superpose b2e66 b2e70616
          | exact resolve b2e70616 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66 b2e70616
        have b2e70618 : False := by grind
        exact b2e70618
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = y := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : False := by grind
        exact b3e27
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e22 : x = y := by grind
          have b4e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : False := by grind
          exact b4e30
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op X0 X1))) := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e54 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e56 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e54
        have b6e58 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e56
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e56
          | exact resolve b6e56 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e95 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e58
             grind)
          | exact superpose b6e58 b6e15
          | exact resolve b6e15 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e97 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e95
        have b6e98 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e97
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e97
          | exact resolve b6e97 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e99 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e98
             have i₂ := b6e55 y
             grind)
          | exact superpose b6e55 b6e98
          | exact resolve b6e98 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e98
        have b6e142 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e99
             grind)
          | exact superpose b6e99 b6e13
          | exact resolve b6e13 b6e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e143 : (k x y) = (M.op y y) := by
          first
          | (have i₁ := b6e142
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e142
          | exact resolve b6e142 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e142
        have b6e196 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e143
             grind)
          | exact superpose b6e143 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e143
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e197 : (M.op x y) = (M.op y y) ∨ x = y := by
          first
          | (have r₁ := b6e196
             have r₂ := b6e20
             grind)
          | exact resolve b6e196 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e196
        have b6e199 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e197
             have r₂ := b6e21
             grind)
          | exact resolve b6e197 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e197
        have b6e233 : (M.op x y) = (M.op y (M.op y (M.op x y))) := by
          first
          | (have i₁ := b6e12 y y
             have i₂ := b6e199
             grind)
          | exact superpose b6e199 b6e12
          | exact resolve b6e12 b6e199
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e199
        have b6e235 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e233
             have i₂ := b6e12 x y
             grind)
          | exact superpose b6e12 b6e233
          | exact resolve b6e233 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e233
        have b6e240 : False := by grind
        exact b6e240
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e46 (σ X0)
               grind)
            | exact superpose b8e46 b8e19
            | exact resolve b8e19 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e49 X0
               have i₂ := b8e46 X0
               grind)
            | exact superpose b8e46 b8e49
            | exact resolve b8e49 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46 b8e49
          have b8e61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e61 X0 X1
               have i₂ := b8e54 X0
               grind)
            | exact superpose b8e54 b8e61
            | (have j0 := b8e61 X0 X1
               grind)
            | exact resolve b8e61 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e1147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e73 x y
               grind)
            | exact superpose b8e73 b8e20
            | (have j1 := b8e73 x y
               grind)
            | exact resolve b8e20 b8e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e73
          have b8e1227 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1147
               have r₂ := b8e24
               grind)
            | exact resolve b8e1147 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1147
          have b8e3707 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e1227
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1227
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1227
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1227
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1227 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1227
          have b8e3708 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by grind
          clear b8e3707
          have b8e3711 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have r₁ := b8e3708
               have r₂ := b8e21
               grind)
            | exact resolve b8e3708 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3708
          have b8e3715 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e3711
               have r₂ := b8e22
               grind)
            | exact resolve b8e3711 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3711
          have b8e3719 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e3715
               grind)
            | exact superpose b8e3715 b8e23
            | exact resolve b8e23 b8e3715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3715
          have b8e3759 : False := by grind
          exact b8e3759
