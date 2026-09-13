import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4297`: `x ◇ (x ◇ y) = y ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4297 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4297 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4297.models_iff G M).mp hM
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
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e50 (σ X0)
           grind)
        | exact superpose b0e50 b0e17
        | exact resolve b0e17 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e56 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e56
        | exact resolve b0e56 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e56
      have b0e381 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e61 x
           grind)
        | exact superpose b0e61 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e61 x
           grind)
        | exact resolve b0e22 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e61
      have b0e397 : False := by grind
      exact b0e397
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
        have b1e55 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e58 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e58
        have b1e63 : (k x y) = (M.op y y) := by grind
        clear b1e55
        have b1e64 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e62
          | exact resolve b1e62 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e65 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e64
             have i₂ := b1e61 y
             grind)
          | exact superpose b1e61 b1e64
          | exact resolve b1e64 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64
        have b1e67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e61 (σ X0)
             grind)
          | exact superpose b1e61 b1e18
          | exact resolve b1e18 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e67 X0
             have i₂ := b1e61 X0
             grind)
          | exact superpose b1e61 b1e67
          | exact resolve b1e67 b1e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61 b1e67
        have b1e82 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e84 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e82 X0
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e82
          | (have j0 := b1e82 X0
             grind)
          | exact resolve b1e82 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82
        have b1e144 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e23
          | exact resolve b1e23 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e3223 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e84 (σ x)
             have i₂ := b1e65
             grind)
          | exact superpose b1e65 b1e84
          | (have j0 := b1e84 (σ x)
             grind)
          | (have r₁ := b1e84 (σ x)
             have r₂ := b1e65
             grind)
          | exact resolve b1e84 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e84
        have b1e3224 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e3223
        have b1e3225 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e3224
             have i₂ := b1e74 x
             grind)
          | exact superpose b1e74 b1e3224
          | exact resolve b1e3224 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3224
        have b1e3226 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e3225
             have r₂ := b1e144
             grind)
          | exact resolve b1e3225 b1e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3225
        have b1e3227 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e3226
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e3226
          | exact resolve b1e3226 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3226
        have b1e3228 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e3227
             have i₂ := b1e63
             grind)
          | exact superpose b1e63 b1e3227
          | exact resolve b1e3227 b1e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e63 b1e3227
        have b1e3229 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e3228
             have i₂ := b1e74 x
             grind)
          | exact superpose b1e74 b1e3228
          | exact resolve b1e3228 b1e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74 b1e3228
        have b1e3230 : False := by grind
        exact b1e3230
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
        have b2e53 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : (k x y) = (M.op y y) := by grind
        clear b2e53
        have b2e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e57 (σ X0)
             grind)
          | exact superpose b2e57 b2e18
          | exact resolve b2e18 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e60 X0
             have i₂ := b2e57 X0
             grind)
          | exact superpose b2e57 b2e60
          | exact resolve b2e60 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e60
        have b2e100 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e201 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e67 y
             grind)
          | exact superpose b2e67 b2e22
          | exact resolve b2e22 b2e67
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e67
        have b2e6364 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e100 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e100
        have b2e6365 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e6364
             have r₂ := b2e21
             grind)
          | exact resolve b2e6364 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6364
        have b2e6366 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e6365
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e6365
          | exact resolve b2e6365 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6365
        have b2e6367 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e6366
             have i₂ := b2e58
             grind)
          | exact superpose b2e58 b2e6366
          | exact resolve b2e6366 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58 b2e6366
        have b2e6368 : False := by grind
        exact b2e6368
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
        have b3e60 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e64 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e60
        have b3e66 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e64
          | exact resolve b3e64 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e64
        have b3e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e63 (σ X0)
             grind)
          | exact superpose b3e63 b3e18
          | exact resolve b3e18 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e76 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e69 X0
             have i₂ := b3e63 X0
             grind)
          | exact superpose b3e63 b3e69
          | exact resolve b3e69 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e69
        have b3e83 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e89 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e15
          | exact resolve b3e15 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66
        have b3e91 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e89
        have b3e93 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e91
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e91
          | exact resolve b3e91 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e94 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e93
             have i₂ := b3e63 y
             grind)
          | exact superpose b3e63 b3e93
          | exact resolve b3e93 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63 b3e93
        have b3e95 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e94
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e94
          | exact resolve b3e94 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e94
        have b3e307 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e76 x
             grind)
          | exact superpose b3e76 b3e23
          | exact resolve b3e23 b3e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e76
        have b3e1708 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e83 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e1709 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e1708
             have r₂ := b3e20
             grind)
          | exact resolve b3e1708 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1708
        have b3e1713 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e95
             have i₂ := b3e1709
             grind)
          | exact superpose b3e1709 b3e95
          | exact resolve b3e95 b3e1709
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e95 b3e1709
        have b3e1717 : False := by grind
        exact b3e1717
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
          have b4e73 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e73
          have b4e80 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e78
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e78
            | exact resolve b4e78 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e82 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e80
               have i₂ := b4e77 y
               grind)
            | exact superpose b4e77 b4e80
            | exact resolve b4e80 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77 b4e80
          have b4e83 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e82
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e82
            | exact resolve b4e82 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e84 : False := by grind
          exact b4e84
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
          have b5e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e73 (σ X0)
               grind)
            | exact superpose b5e73 b5e19
            | exact resolve b5e19 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e86 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e77 X0
               have i₂ := b5e73 X0
               grind)
            | exact superpose b5e73 b5e77
            | exact resolve b5e77 b5e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e73 b5e77
          have b5e95 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e142 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e1880 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e95 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e95
          have b5e1881 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e1880
               have r₂ := b5e21
               grind)
            | exact resolve b5e1880 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1880
          have b5e12038 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e142 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e142
          have b5e12039 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e12038
               have r₂ := b5e23
               grind)
            | exact resolve b5e12038 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12038
          have b5e12040 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e12039
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e12039
            | exact resolve b5e12039 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12039
          have b5e12041 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e12040
               have i₂ := b5e1881
               grind)
            | exact superpose b5e1881 b5e12040
            | exact resolve b5e12040 b5e1881
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1881 b5e12040
          have b5e12044 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e12041
               grind)
            | exact superpose b5e12041 b5e23
            | exact resolve b5e23 b5e12041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e12041
          have b5e12077 : False := by grind
          exact b5e12077
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
        have b6e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e58 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e56
        have b6e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e59
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e59
          | exact resolve b6e59 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59
        have b6e81 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e15
          | exact resolve b6e15 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e83 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e81
        have b6e84 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e83
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e83
          | exact resolve b6e83 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83
        have b6e85 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e84
             have i₂ := b6e58 y
             grind)
          | exact superpose b6e58 b6e84
          | exact resolve b6e84 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e84
        have b6e146 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e85
             grind)
          | exact superpose b6e85 b6e13
          | exact resolve b6e13 b6e85
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e147 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e146
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e146
          | exact resolve b6e146 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e146
        have b6e210 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e147
             grind)
          | exact superpose b6e147 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e147
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e147
        have b6e211 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e210
        have b6e213 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e211
             have r₂ := b6e21
             grind)
          | exact resolve b6e211 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e211
        have b6e215 : False := by grind
        exact b6e215
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
          have b7e70 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e74 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e70
          have b7e75 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e74
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e74
            | exact resolve b7e74 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e76 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e75
               have i₂ := b7e73 y
               grind)
            | exact superpose b7e73 b7e75
            | exact resolve b7e75 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75
          have b7e78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e73 (σ X0)
               grind)
            | exact superpose b7e73 b7e19
            | exact resolve b7e19 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e87 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e78 X0
               have i₂ := b7e73 X0
               grind)
            | exact superpose b7e73 b7e78
            | exact resolve b7e78 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e78
          have b7e97 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e99 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e97 X0
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e97
            | (have j0 := b7e97 X0
               grind)
            | exact resolve b7e97 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e100 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e23
            | exact resolve b7e23 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e105 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e100
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e100
            | exact resolve b7e100 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e149 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e118 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e118
          have b7e4063 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e99 (σ x)
               have i₂ := b7e76
               grind)
            | exact superpose b7e76 b7e99
            | (have j0 := b7e99 (σ x)
               grind)
            | (have r₁ := b7e99 (σ x)
               have r₂ := b7e76
               grind)
            | exact resolve b7e99 b7e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e76 b7e99
          have b7e4065 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e4063
          have b7e4066 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e4065
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e4065
            | exact resolve b7e4065 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4065
          have b7e4067 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e4066
               have r₂ := b7e105
               grind)
            | exact resolve b7e4066 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4066
          have b7e4068 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e4067
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e4067
            | exact resolve b7e4067 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4067
          have b7e4069 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e4068
               have i₂ := b7e87 x
               grind)
            | exact superpose b7e87 b7e4068
            | exact resolve b7e4068 b7e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87 b7e4068
          have b7e4071 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e4069
               have i₂ := b7e149 x y
               grind)
            | exact superpose b7e149 b7e4069
            | (have j1 := b7e149 x y
               grind)
            | exact resolve b7e4069 b7e149
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e149
          have b7e4078 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e4069
               grind)
            | exact superpose b7e4069 b7e14
            | exact resolve b7e14 b7e4069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4069
          have b7e4079 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e4078
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e4078
            | exact resolve b7e4078 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4078
          have b7e4086 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e4071
               have r₂ := b7e105
               grind)
            | exact resolve b7e4071 b7e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105 b7e4071
          have b7e4089 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e4086
               have r₂ := b7e22
               grind)
            | exact resolve b7e4086 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4086
          have b7e4090 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e4089
               have i₂ := b7e4079
               grind)
            | exact superpose b7e4079 b7e4089
            | exact resolve b7e4089 b7e4079
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e4079 b7e4089
          have b7e4091 : False := by grind
          exact b7e4091
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
          have b8e134 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e7695 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e134 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e7696 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e7695
               have r₂ := b8e23
               grind)
            | exact resolve b8e7695 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7695
          have b8e7697 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e7696
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e7696
            | exact resolve b8e7696 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7696
          have b8e7702 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e7697
               grind)
            | exact superpose b8e7697 b8e20
            | exact resolve b8e20 b8e7697
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7697
          have b8e7950 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e7702
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e7702
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e7702 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7702
          have b8e7951 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e7950
          have b8e7953 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e7951
               have r₂ := b8e21
               grind)
            | exact resolve b8e7951 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e7951
          have b8e7956 : False := by grind
          exact b8e7956

/-- `Equation4439`: `x ◇ (y ◇ x) = (x ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_x_pxy_Equation4439 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4439 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4439.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = a :=
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
      have b0e65 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e68 : False := by grind
      exact b0e68
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
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
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X0) X3) X0) = (M.op (M.op X2 X0) (M.op (M.op X0 X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X2 X0) X0 X3
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X1 (M.op X0 X2) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X2 X3
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e44 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 x)) := by
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
          have b5e45 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X3 (M.op X2 X0)
               have i₂ := b5e13 X0 X2 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e46 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 (M.op X0 X2) X3 X1
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e46 X0 x X2 X3
               have i₂ := b5e13 X0 X3 (M.op x X0)
               grind)
            | exact superpose b5e13 b5e46
            | exact resolve b5e46 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e49 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op x (M.op X0 (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e44 (M.op X0 X1)
               have i₂ := b5e13 X0 x X1
               grind)
            | exact superpose b5e13 b5e44
            | exact resolve b5e44 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e50 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X1 (M.op X0 x)
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e13
            | exact resolve b5e13 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e53 : ∀ X1 : G, (M.op x (M.op X1 x)) = (M.op y (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b5e50 x X1
               have i₂ := b5e13 y X1 x
               grind)
            | exact superpose b5e13 b5e50
            | exact resolve b5e50 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e54 : ∀ X1 : G, (M.op y X1) = (M.op y (M.op X1 y)) := by
            intro X1
            first
            | (have i₁ := b5e53 X1
               have i₂ := b5e44 X1
               grind)
            | exact superpose b5e44 b5e53
            | exact resolve b5e53 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e53
          have b5e55 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e59 : x = y ∨ x = (k x y) := by grind
          clear b5e55
          have b5e60 : x = (k x y) := by
            first
            | (have r₁ := b5e59
               have r₂ := b5e21
               grind)
            | exact resolve b5e59 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59
          have b5e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e67 : (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b5e54 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e54
            | exact resolve b5e54 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e92 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ X0) X1 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e13
            | exact resolve b5e13 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e123 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e42 (σ X0) X1 X2 (σ X0)
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e42
            | exact resolve b5e42 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e200 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (M.op (σ (M.op X0 X0)) X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e45 (σ X0) (σ X0) X2 X1
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e45
            | exact resolve b5e45 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e244 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (M.op (σ (M.op X0 X0)) X2) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e200 X0 X1 X2
               have i₂ := b5e92 X0 X1
               grind)
            | exact superpose b5e92 b5e200
            | exact resolve b5e200 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e200
          have b5e325 : ∀ X0 X1 X2 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X0 X1) (M.op x X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e41 x X0 X2 X1
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e41
            | exact resolve b5e41 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e336 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 (M.op X1 X2) x
               have i₂ := b5e41 X1 X0 X2 x
               grind)
            | exact superpose b5e41 b5e13
            | exact resolve b5e13 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e437 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e48 (σ X0) (σ X0) x
               have i₂ := b5e31 X0
               grind)
            | exact superpose b5e31 b5e48
            | exact resolve b5e48 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e439 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op (M.op y X0) (M.op X1 (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e48 x (M.op X0 x) x
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e48
            | exact resolve b5e48 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e462 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e41 X1 X0 (M.op X0 x) x
               have i₂ := b5e48 X0 x X1
               grind)
            | exact superpose b5e48 b5e41
            | exact resolve b5e41 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e466 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 (M.op X0 X2)) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 (M.op X1 (M.op X0 X2)) X2
               have i₂ := b5e48 X0 X2 X1
               grind)
            | exact superpose b5e48 b5e13
            | exact resolve b5e13 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e494 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op y (M.op (M.op X1 (M.op y X0)) y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e439 X0 X1
               have i₂ := b5e13 y (M.op X1 (M.op y X0)) X0
               grind)
            | exact superpose b5e13 b5e439
            | exact resolve b5e439 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e439
          have b5e496 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e437 X0 X1
               have i₂ := b5e92 (M.op X0 X0) X1
               grind)
            | exact superpose b5e92 b5e437
            | exact resolve b5e437 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e437
          have b5e506 : ∀ X0 X1 : G, (M.op x (M.op X1 x)) = (M.op y (M.op X1 (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e494 X0 X1
               have i₂ := b5e54 (M.op X1 (M.op y X0))
               grind)
            | (have i₁ := b5e494 X0 X1
               have i₂ := b5e54 (M.op (M.op X1 (M.op y X0)) y)
               grind)
            | exact superpose b5e54 b5e494
            | exact resolve b5e494 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e54 b5e494
          have b5e507 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e496 X0 X1
               have i₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b5e13 b5e496
            | exact resolve b5e496 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e496
          have b5e511 : ∀ X0 X1 : G, (M.op y X1) = (M.op y (M.op X1 (M.op y X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e506 X0 X1
               have i₂ := b5e44 X1
               grind)
            | exact superpose b5e44 b5e506
            | exact resolve b5e506 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e506
          have b5e512 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 (M.op X0 (M.op X0 X0)))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e507 X0 X1
               have i₂ := b5e336 X0 X0 X0
               grind)
            | exact superpose b5e336 b5e507
            | exact resolve b5e507 b5e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e507
          have b5e514 : ∀ X0 X1 : G, (M.op (σ X0) (M.op X1 (σ X0))) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e512 X0 X1
               have i₂ := b5e462 X0 X0
               grind)
            | exact superpose b5e462 b5e512
            | exact resolve b5e512 b5e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e512
          have b5e515 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e514 X0 X1
               have i₂ := b5e92 X0 X1
               grind)
            | exact superpose b5e92 b5e514
            | exact resolve b5e514 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e514
          have b5e554 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X3) X1) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X1 X4) (M.op X0 X2))) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e40 X1 X1 (M.op X0 X2) X3
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e40
            | exact resolve b5e40 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e40
          have b5e675 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X3) X1) = (M.op X0 (M.op (M.op (M.op X1 X4) (M.op X0 X2)) X0)) := by
            intro X0 X1 X2 X3 X4
            first
            | (have i₁ := b5e554 X0 X1 X2 X3 X4
               have i₂ := b5e13 X0 (M.op (M.op X1 X4) (M.op X0 X2)) (M.op X1 X0)
               grind)
            | exact superpose b5e13 b5e554
            | exact resolve b5e554 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e554
          have b5e714 : ∀ X0 X1 X3 X4 : G, (M.op (M.op (M.op X0 (M.op X1 X0)) X3) X1) = (M.op X0 (M.op (M.op X1 X4) X0)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b5e675 X0 X1 x X3 X4
               have i₂ := b5e466 X0 (M.op X1 X4) x
               grind)
            | exact superpose b5e466 b5e675
            | exact resolve b5e675 b5e466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e466 b5e675
          have b5e732 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X1 X4) X0)) := by
            intro X0 X1 X4
            first
            | (have i₁ := b5e714 X0 X1 x X4
               have i₂ := b5e45 X0 (M.op X1 X0) x X1
               grind)
            | exact superpose b5e45 b5e714
            | exact resolve b5e714 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45 b5e714
          have b5e1323 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op y (M.op (M.op X0 X1) (M.op y X2))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e511 (M.op X0 y) X0
               have i₂ := b5e41 y X0 X2 X1
               grind)
            | exact superpose b5e41 b5e511
            | exact resolve b5e511 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1369 : ∀ X0 X1 : G, (M.op y X0) = (M.op y (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e1323 X0 X1 x
               have i₂ := b5e511 x (M.op X0 X1)
               grind)
            | exact superpose b5e511 b5e1323
            | exact resolve b5e1323 b5e511
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e511 b5e1323
          have b5e1391 : ∀ X0 X1 X2 : G, (M.op (σ X0) (M.op X2 (σ X0))) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 (σ X0) X2 (σ X1)
               have i₂ := b5e63 X0 X1
               grind)
            | exact superpose b5e63 b5e13
            | (have j1 := b5e63 X0 X1
               grind)
            | exact resolve b5e13 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1414 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (M.op (σ (k X0 X1)) X2) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e1391 X0 X1 X2
               have i₂ := b5e92 X0 X2
               grind)
            | exact superpose b5e92 b5e1391
            | (have j0 := b5e1391 X0 X1 X2
               grind)
            | exact resolve b5e1391 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1391
          have b5e1863 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 x) (M.op y X0))) = (M.op y (M.op (M.op X0 x) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e49 (M.op X0 x) X1
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e49
            | exact resolve b5e49 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e2009 : ∀ X0 : G, (M.op x (M.op (M.op X0 x) (M.op y X0))) = (M.op y (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e1863 X0 x
               have i₂ := b5e1369 (M.op X0 x) x
               grind)
            | exact superpose b5e1369 b5e1863
            | exact resolve b5e1863 b5e1369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1863
          have b5e2086 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op (M.op X0 x) (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e2009 X0
               have i₂ := b5e1369 X0 x
               grind)
            | exact superpose b5e1369 b5e2009
            | exact resolve b5e2009 b5e1369
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1369 b5e2009
          have b5e2133 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op y (M.op X0 y)))) := by
            intro X0
            first
            | (have i₁ := b5e2086 X0
               have i₂ := b5e41 y X0 X0 x
               grind)
            | exact superpose b5e41 b5e2086
            | exact resolve b5e2086 b5e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2086
          have b5e2158 : ∀ X0 : G, (M.op y X0) = (M.op x (M.op X0 (M.op y X0))) := by
            intro X0
            first
            | (have i₁ := b5e2133 X0
               have i₂ := b5e462 X0 y
               grind)
            | exact superpose b5e462 b5e2133
            | exact resolve b5e2133 b5e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2133
          have b5e2859 : ∀ X0 X1 : G, (M.op y X0) = (M.op x (M.op (M.op X0 X1) y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e2158 X0
               have i₂ := b5e13 X0 y X1
               grind)
            | exact superpose b5e13 b5e2158
            | exact resolve b5e2158 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2158
          have b5e3055 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X1)) X2) X3) = (M.op (σ (M.op X0 (M.op (M.op X0 X1) X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e123 (M.op X0 X1) X2 X3
               have i₂ := b5e13 X0 (M.op X0 X1) X1
               grind)
            | exact superpose b5e13 b5e123
            | exact resolve b5e123 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3127 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e31 (M.op X0 X0)
               have i₂ := b5e123 X0 X1 (σ (M.op X0 X0))
               grind)
            | exact superpose b5e123 b5e31
            | exact resolve b5e31 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e3129 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (σ (M.op X0 X0))) = (M.op X2 (M.op (M.op (σ X0) X1) X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 (σ (M.op X0 X0)) X3
               have i₂ := b5e123 X0 X1 X2
               grind)
            | exact superpose b5e123 b5e13
            | exact resolve b5e13 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3158 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (σ (M.op X0 X0)) X2)) = (M.op (M.op X2 X3) (M.op (M.op (σ X0) X1) (M.op X2 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e48 X2 X3 (σ (M.op X0 X0))
               have i₂ := b5e123 X0 X1 (M.op X2 X3)
               grind)
            | exact superpose b5e123 b5e48
            | exact resolve b5e48 b5e123
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e3177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 X0)) X2)) = (M.op X2 (M.op (M.op (σ X0) X1) X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e3158 X0 X1 X2 x
               have i₂ := b5e48 X2 x (M.op (σ X0) X1)
               grind)
            | exact superpose b5e48 b5e3158
            | exact resolve b5e3158 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3158
          have b5e3199 : ∀ X0 X2 X3 : G, (M.op X2 (M.op (σ X0) X2)) = (M.op (M.op X2 X3) (σ (M.op X0 X0))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b5e3129 X0 x X2 X3
               have i₂ := b5e732 X2 (σ X0) x
               grind)
            | exact superpose b5e732 b5e3129
            | exact resolve b5e3129 b5e732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3129
          have b5e3200 : ∀ X0 X1 : G, (σ (M.op X0 (M.op (M.op X0 X0) X0))) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b5e3127 X0 X1
               have i₂ := b5e13 X0 (M.op X0 X0) X0
               grind)
            | exact superpose b5e13 b5e3127
            | exact resolve b5e3127 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3127
          have b5e3244 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ (M.op X0 X1)) X2) X3) = (M.op (σ (M.op X0 (M.op X0 X0))) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e3055 X0 X1 X2 X3
               have i₂ := b5e732 X0 X0 X1
               grind)
            | exact superpose b5e732 b5e3055
            | exact resolve b5e3055 b5e732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3055
          have b5e3265 : ∀ X0 X2 : G, (M.op X2 (M.op (σ X0) X2)) = (M.op X2 (M.op (σ (M.op X0 X0)) X2)) := by
            intro X0 X2
            first
            | (have i₁ := b5e3177 X0 x X2
               have i₂ := b5e732 X2 (σ X0) x
               grind)
            | exact superpose b5e732 b5e3177
            | exact resolve b5e3177 b5e732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e732 b5e3177
          have b5e3280 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op (M.op X0 X0) X0))) := by
            intro X0
            first
            | (have i₁ := b5e3200 X0 x
               have i₂ := b5e3199 X0 (σ X0) x
               grind)
            | exact superpose b5e3199 b5e3200
            | exact resolve b5e3200 b5e3199
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3199 b5e3200
          have b5e3331 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b5e3280 X0
               have i₂ := b5e336 X0 X0 X0
               grind)
            | exact superpose b5e336 b5e3280
            | exact resolve b5e3280 b5e336
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e336 b5e3280
          have b5e3358 : ∀ X0 : G, (M.op (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b5e3331 X0
               have i₂ := b5e462 X0 X0
               grind)
            | exact superpose b5e462 b5e3331
            | exact resolve b5e3331 b5e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3331
          have b5e3373 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e3358 X0
               have i₂ := b5e92 X0 (σ X0)
               grind)
            | exact superpose b5e92 b5e3358
            | exact resolve b5e3358 b5e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92 b5e3358
          have b5e3625 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x X0)) X1) X2) = (M.op (σ (M.op x (M.op y x))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e123 (M.op x X0) X1 X2
               have i₂ := b5e325 x X0 X0
               grind)
            | exact superpose b5e325 b5e123
            | exact resolve b5e123 b5e325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e123 b5e325
          have b5e3660 : ∀ X0 X1 X2 : G, (M.op (M.op (σ (M.op x X0)) X1) X2) = (M.op (σ (M.op y y)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e3625 X0 X1 X2
               have i₂ := b5e44 y
               grind)
            | exact superpose b5e44 b5e3625
            | exact resolve b5e3625 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3625
          have b5e3757 : ∀ X2 : G, (M.op (σ (M.op y y)) X2) = (M.op (σ (M.op x (M.op x x))) X2) := by
            intro X2
            first
            | (have i₁ := b5e3660 x x X2
               have i₂ := b5e3244 x x x X2
               grind)
            | exact superpose b5e3244 b5e3660
            | exact resolve b5e3660 b5e3244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3244 b5e3660
          have b5e3835 : ∀ X2 : G, (M.op (σ (M.op y y)) X2) = (M.op (σ (M.op x x)) X2) := by
            intro X2
            first
            | (have i₁ := b5e3757 X2
               have i₂ := b5e515 x X2
               grind)
            | exact superpose b5e515 b5e3757
            | exact resolve b5e3757 b5e515
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e515 b5e3757
          have b5e4107 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) (M.op X1 X3)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e41 X1 X0 X3 X2
               have i₂ := b5e462 X0 X1
               grind)
            | exact superpose b5e462 b5e41
            | exact resolve b5e41 b5e462
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41 b5e462
          have b5e26142 : ∀ X0 X1 : G, (M.op X0 (M.op (σ (M.op x x)) X0)) = (M.op (M.op X0 X1) (M.op (σ (M.op y y)) (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e48 X0 X1 (σ (M.op x x))
               have i₂ := b5e3835 (M.op X0 X1)
               grind)
            | exact superpose b5e3835 b5e48
            | exact resolve b5e48 b5e3835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e26211 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x x)) X0)) = (M.op X0 (M.op (σ (M.op y y)) X0)) := by
            intro X0
            first
            | (have i₁ := b5e26142 X0 x
               have i₂ := b5e4107 X0 (σ (M.op y y)) x (M.op X0 x)
               grind)
            | exact superpose b5e4107 b5e26142
            | exact resolve b5e26142 b5e4107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e4107 b5e26142
          have b5e26362 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op x x)) X0)) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b5e26211 X0
               have i₂ := b5e3265 y X0
               grind)
            | (have i₁ := b5e26211 x
               have i₂ := b5e3265 (M.op y y) x
               grind)
            | exact superpose b5e3265 b5e26211
            | exact resolve b5e26211 b5e3265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26211
          have b5e26502 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op X0 (M.op (σ x) X0)) := by
            intro X0
            first
            | (have i₁ := b5e26362 X0
               have i₂ := b5e3265 x X0
               grind)
            | (have i₁ := b5e26362 x
               have i₂ := b5e3265 (M.op x x) x
               grind)
            | exact superpose b5e3265 b5e26362
            | exact resolve b5e26362 b5e3265
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3265 b5e26362
          have b5e61949 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (M.op X0 X1) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 (σ x) X1
               have i₂ := b5e26502 X0
               grind)
            | exact superpose b5e26502 b5e13
            | exact resolve b5e13 b5e26502
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e26502
          have b5e228683 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1414 x y X0
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e1414
            | (have j0 := b5e1414 x y x
               grind)
            | exact resolve b5e1414 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1414
          have b5e230131 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) := by
            intro X0
            first
            | (have j0 := b5e228683 X0
               grind)
            | (have r₁ := b5e228683 X0
               have r₂ := b5e24
               grind)
            | exact resolve b5e228683 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e228683
          have b5e230849 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b5e230131 X0
               grind)
            | (have r₁ := b5e230131 X0
               have r₂ := b5e23
               grind)
            | exact resolve b5e230131 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e230131
          have b5e231830 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e3835 X0
               have i₂ := b5e230849 X0
               grind)
            | exact superpose b5e230849 b5e3835
            | exact resolve b5e3835 b5e230849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e232065 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x x)) X1) X0) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (σ (M.op x x)) X0 X1
               have i₂ := b5e230849 (M.op X0 (σ (M.op x x)))
               grind)
            | exact superpose b5e230849 b5e13
            | exact resolve b5e13 b5e230849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e232141 : ∀ X0 : G, (M.op (M.op (σ (M.op x x)) X0) (σ x)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e61949 (σ (M.op x x)) X0
               have i₂ := b5e230849 (M.op (σ y) (σ (M.op x x)))
               grind)
            | exact superpose b5e230849 b5e61949
            | exact resolve b5e61949 b5e230849
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61949 b5e230849
          have b5e232205 : (M.op (σ (M.op x x)) (σ x)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e232141 x
               have i₂ := b5e244 x (σ x) x
               grind)
            | exact superpose b5e244 b5e232141
            | exact resolve b5e232141 b5e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232141
          have b5e232274 : ∀ X0 : G, (M.op (σ (M.op x x)) X0) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e232065 X0 x
               have i₂ := b5e244 x X0 x
               grind)
            | exact superpose b5e244 b5e232065
            | exact resolve b5e232065 b5e244
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244 b5e232065
          have b5e232533 : (σ (M.op x (M.op x x))) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e232205
               have i₂ := b5e3373 x
               grind)
            | exact superpose b5e3373 b5e232205
            | exact resolve b5e232205 b5e3373
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3373 b5e232205
          have b5e232601 : ∀ X0 : G, (M.op (σ (M.op y y)) X0) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e232274 X0
               have i₂ := b5e3835 X0
               grind)
            | exact superpose b5e3835 b5e232274
            | exact resolve b5e232274 b5e3835
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3835 b5e232274
          have b5e232807 : (σ (M.op y x)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e232533
               have i₂ := b5e44 x
               grind)
            | exact superpose b5e44 b5e232533
            | exact resolve b5e232533 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e232533
          have b5e232855 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
            intro X0
            first
            | (have i₁ := b5e232601 X0
               have i₂ := b5e231830 X0
               grind)
            | exact superpose b5e231830 b5e232601
            | exact resolve b5e232601 b5e231830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e231830 b5e232601
          have b5e233011 : (σ (M.op y y)) = (M.op (σ x) (M.op (σ y) (σ (M.op x x)))) := by
            first
            | (have i₁ := b5e232807
               have i₂ := b5e67
               grind)
            | exact superpose b5e67 b5e232807
            | exact resolve b5e232807 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e232807
          have b5e233145 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e233011
               have i₂ := b5e232855 (σ y)
               grind)
            | exact superpose b5e232855 b5e233011
            | exact resolve b5e233011 b5e232855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e232855 b5e233011
          have b5e239399 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e233145
               grind)
            | exact superpose b5e233145 b5e24
            | exact resolve b5e24 b5e233145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e239400 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e63 x y
               have i₂ := b5e233145
               grind)
            | exact superpose b5e233145 b5e63
            | (have j0 := b5e63 (k x y) (M.op y y)
               grind)
            | exact resolve b5e63 b5e233145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e233145
          have b5e239743 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e239400
               have r₂ := b5e23
               grind)
            | exact resolve b5e239400 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e239400
          have b5e239875 : (σ (k x y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e239743
               have r₂ := b5e239399
               grind)
            | exact resolve b5e239743 b5e239399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e239399 b5e239743
          have b5e239963 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e239875
               have i₂ := b5e60
               grind)
            | exact superpose b5e60 b5e239875
            | exact resolve b5e239875 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60 b5e239875
          have b5e246760 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b5e14 (M.op y y)
               have i₂ := b5e239963
               grind)
            | exact superpose b5e239963 b5e14
            | exact resolve b5e14 b5e239963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e239963
          have b5e246820 : x = (M.op y y) := by
            first
            | (have i₁ := b5e246760
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e246760
            | exact resolve b5e246760 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e246760
          have b5e248667 : x = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b5e2859 y y
               have i₂ := b5e246820
               grind)
            | exact superpose b5e246820 b5e2859
            | exact resolve b5e2859 b5e246820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2859 b5e246820
          have b5e248706 : x = (M.op x y) := by
            first
            | (have i₁ := b5e248667
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e248667
            | exact resolve b5e248667 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248667
          have b5e248838 : x = y := by
            first
            | (have i₁ := b5e248706
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e248706
            | exact resolve b5e248706 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248706
          have b5e248932 : False := by grind
          exact b5e248932
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X1) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X3) (M.op X0 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X1 (M.op X0 X2) X3
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X2 X3
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b7e13 (σ x) X0 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X3 (M.op X2 X0)
               have i₂ := b7e13 X0 X2 X1
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 X0)) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 (M.op X0 X2) X3 X1
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op X0 (M.op (M.op X3 (M.op X0 X1)) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 (M.op X3 (M.op X0 X1)) X1
               have i₂ := b7e13 (M.op X0 X1) X3 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e42 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X0 X2) (M.op X3 (M.op X0 X2))) := by
            intro X0 X2 X3
            first
            | (have i₁ := b7e40 X0 x X2 X3
               have i₂ := b7e13 X0 X3 (M.op x X0)
               grind)
            | exact superpose b7e13 b7e40
            | exact resolve b7e40 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e51 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e54 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e51
          have b7e55 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e23
               grind)
            | exact resolve b7e54 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e54
          have b7e56 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e55
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e55
            | exact resolve b7e55 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e59 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e56
               grind)
            | exact superpose b7e56 b7e14
            | exact resolve b7e14 b7e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : x = (k x y) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e59
            | exact resolve b7e59 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e70 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e60
               grind)
            | exact superpose b7e60 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e71 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e22
               grind)
            | exact resolve b7e70 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : x = (M.op x y) := by
            first
            | (have r₁ := b7e71
               have r₂ := b7e21
               grind)
            | exact resolve b7e71 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e90 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b7e13 x X0 y
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e13
            | exact resolve b7e13 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e124 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 (σ x) X0 X1 (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e125 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (M.op X0 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e36 (σ X0) X1 X2 (σ X0)
               have i₂ := b7e31 X0
               grind)
            | exact superpose b7e31 b7e36
            | exact resolve b7e36 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e142 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op x x)) X1) := by
            intro X1
            first
            | (have i₁ := b7e124 x X1
               have i₂ := b7e125 x x X1
               grind)
            | exact superpose b7e125 b7e124
            | exact resolve b7e124 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e124
          have b7e167 : ∀ X0 X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ x) X1 (M.op X0 (σ x))
               have i₂ := b7e38 X0
               grind)
            | exact superpose b7e38 b7e13
            | exact resolve b7e13 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e170 : ∀ X1 : G, (M.op (σ x) (M.op X1 (σ x))) = (M.op (σ (M.op y y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e167 x X1
               have i₂ := b7e125 y x X1
               grind)
            | exact superpose b7e125 b7e167
            | exact resolve b7e167 b7e125
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e125 b7e167
          have b7e178 : ∀ X1 : G, (M.op (σ y) X1) = (M.op (σ (M.op y y)) X1) := by
            intro X1
            first
            | (have i₁ := b7e170 X1
               have i₂ := b7e38 X1
               grind)
            | exact superpose b7e38 b7e170
            | exact resolve b7e170 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e170
          have b7e411 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) = (M.op X0 (M.op (M.op X1 X2) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X0 (M.op X1 X2) x
               have i₂ := b7e35 X1 X0 X2 x
               grind)
            | exact superpose b7e35 b7e13
            | exact resolve b7e13 b7e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e546 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X1 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b7e35 X1 X0 (M.op X0 x) x
               have i₂ := b7e42 X0 x X1
               grind)
            | exact superpose b7e42 b7e35
            | exact resolve b7e35 b7e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e35 b7e42
          have b7e1145 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e31 (M.op x x)
               have i₂ := b7e142 (σ (M.op x x))
               grind)
            | exact superpose b7e142 b7e31
            | exact resolve b7e31 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1167 : (M.op (σ x) (M.op (σ y) (σ x))) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e38 (σ (M.op x x))
               have i₂ := b7e142 (σ x)
               grind)
            | exact superpose b7e142 b7e38
            | exact resolve b7e38 b7e142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e142
          have b7e1170 : (M.op (σ y) (σ y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e1167
               have i₂ := b7e38 (σ y)
               grind)
            | exact superpose b7e38 b7e1167
            | exact resolve b7e1167 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e1167
          have b7e1189 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op (M.op x x) x))) := by
            first
            | (have i₁ := b7e1145
               have i₂ := b7e13 x (M.op x x) x
               grind)
            | exact superpose b7e13 b7e1145
            | exact resolve b7e1145 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1145
          have b7e1195 : (σ (M.op y y)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e1170
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e1170
            | exact resolve b7e1170 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1170
          have b7e1212 : (M.op (σ y) (σ (M.op x x))) = (σ (M.op x (M.op x x))) := by
            first
            | (have i₁ := b7e1189
               have i₂ := b7e90 (M.op x x)
               grind)
            | exact superpose b7e90 b7e1189
            | exact resolve b7e1189 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1189
          have b7e1228 : (σ (M.op x x)) = (M.op (σ y) (σ (M.op x x))) := by
            first
            | (have i₁ := b7e1212
               have i₂ := b7e90 x
               grind)
            | exact superpose b7e90 b7e1212
            | exact resolve b7e1212 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1212
          have b7e1238 : (σ (M.op y y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e1228
               have i₂ := b7e1195
               grind)
            | exact superpose b7e1195 b7e1228
            | exact resolve b7e1228 b7e1195
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1195 b7e1228
          have b7e1316 : (M.op x x) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e1238
               grind)
            | exact superpose b7e1238 b7e14
            | exact resolve b7e14 b7e1238
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1238
          have b7e1317 : (M.op y y) = (M.op x x) := by
            first
            | (have i₁ := b7e1316
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e1316
            | exact resolve b7e1316 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1316
          have b7e1409 : (M.op y y) = (M.op x (M.op y y)) := by
            first
            | (have i₁ := b7e90 x
               have i₂ := b7e1317
               grind)
            | exact superpose b7e1317 b7e90
            | exact resolve b7e90 b7e1317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1417 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op (M.op (M.op y y) X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e39 x x X1 X0
               have i₂ := b7e1317
               grind)
            | exact superpose b7e1317 b7e39
            | exact resolve b7e39 b7e1317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e1425 : ∀ X0 : G, (M.op x (M.op X0 x)) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e1417 X0 x
               have i₂ := b7e39 y y x X0
               grind)
            | exact superpose b7e39 b7e1417
            | exact resolve b7e1417 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1417
          have b7e1435 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b7e1425 X0
               have i₂ := b7e90 X0
               grind)
            | exact superpose b7e90 b7e1425
            | exact resolve b7e1425 b7e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e90 b7e1425
          have b7e1520 : ∀ X0 : G, (M.op y (M.op (M.op y y) y)) = (M.op (M.op (M.op y y) X0) x) := by
            intro X0
            first
            | (have i₁ := b7e41 y y X0 x
               have i₂ := b7e1409
               grind)
            | exact superpose b7e1409 b7e41
            | exact resolve b7e41 b7e1409
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41 b7e1409
          have b7e1552 : (M.op y (M.op x y)) = (M.op y (M.op (M.op y y) y)) := by
            first
            | (have i₁ := b7e1520 x
               have i₂ := b7e39 y y x x
               grind)
            | exact superpose b7e39 b7e1520
            | exact resolve b7e1520 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39 b7e1520
          have b7e1564 : (M.op y (M.op x y)) = (M.op y (M.op y (M.op y y))) := by
            first
            | (have i₁ := b7e1552
               have i₂ := b7e411 y y y
               grind)
            | exact superpose b7e411 b7e1552
            | exact resolve b7e1552 b7e411
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e411 b7e1552
          have b7e1571 : (M.op y (M.op x y)) = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b7e1564
               have i₂ := b7e546 y y
               grind)
            | exact superpose b7e546 b7e1564
            | exact resolve b7e1564 b7e546
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e546 b7e1564
          have b7e1575 : (M.op x y) = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b7e1571
               have i₂ := b7e1435 y
               grind)
            | exact superpose b7e1435 b7e1571
            | exact resolve b7e1571 b7e1435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1571
          have b7e1578 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e1575
               have i₂ := b7e1435 x
               grind)
            | exact superpose b7e1435 b7e1575
            | exact resolve b7e1575 b7e1435
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1435 b7e1575
          have b7e1581 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e1578
               have i₂ := b7e1317
               grind)
            | exact superpose b7e1317 b7e1578
            | exact resolve b7e1578 b7e1317
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1317 b7e1578
          have b7e1584 : x = (M.op y y) := by
            first
            | (have i₁ := b7e1581
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e1581
            | exact resolve b7e1581 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73 b7e1581
          have b7e1723 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b7e178 X0
               have i₂ := b7e1584
               grind)
            | exact superpose b7e1584 b7e178
            | exact resolve b7e178 b7e1584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e178
          have b7e3536 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e1723 (σ y)
               grind)
            | exact superpose b7e1723 b7e24
            | exact resolve b7e24 b7e1723
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1723
          have b7e3607 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e3536
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e3536
            | exact resolve b7e3536 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31 b7e3536
          have b7e3640 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e3607
               have i₂ := b7e1584
               grind)
            | exact superpose b7e1584 b7e3607
            | exact resolve b7e3607 b7e1584
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1584 b7e3607
          have b7e3659 : False := by grind
          exact b7e3659
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
          have b8e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1513 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e62 x y
               grind)
            | exact superpose b8e62 b8e20
            | (have j1 := b8e62 x y
               grind)
            | exact resolve b8e20 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1547 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1513
               have r₂ := b8e24
               grind)
            | exact resolve b8e1513 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1513
          have b8e1556 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1547
               have r₂ := b8e23
               grind)
            | exact resolve b8e1547 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1547
          have b8e1561 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e1556
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1556
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1556
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1556
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1556 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1556
          have b8e1562 : y = (M.op x y) ∨ x = y := by grind
          clear b8e1561
          have b8e1563 : x = y := by
            first
            | (have r₁ := b8e1562
               have r₂ := b8e22
               grind)
            | exact resolve b8e1562 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1562
          have b8e1564 : False := by grind
          exact b8e1564

/-- `Equation4546`: `x ◇ (y ◇ z) = (z ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_x_x_pxy_Equation4546 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4546 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4546.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
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
      have b0e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
      have b0e40 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
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
      have b0e41 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
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
      have b0e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e11 X3 X1 X2
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op X3 (M.op X1 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X2 X3 (M.op X1 X0)
           have i₂ := b0e11 (M.op (M.op X1 X0) X3) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e41 X0
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e41
        | exact resolve b0e41 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e51 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op y x)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 y
           have i₂ := b0e41 X1
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e51 X0 x
           have i₂ := b0e41 (M.op y x)
           grind)
        | exact superpose b0e41 b0e51
        | exact resolve b0e51 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X2 X2) ∨ (k X2 (M.op X1 X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X2 (M.op X1 X0)
           have i₂ := b0e11 X2 X1 X0
           grind)
        | exact superpose b0e11 b0e15
        | (have j0 := b0e15 X2 (M.op X1 X0)
           grind)
        | exact resolve b0e15 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e96 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X2 X0) ∨ (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X0
           have i₂ := b0e16 X0 X1
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
      have b0e97 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (M.op (M.op X1 X2) X0) ∨ (M.op (M.op X2 X1) X2) = X0 ∨ (M.op (M.op X1 X2) X0) = X0 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 (M.op X1 X2) X1 X2
           have i₂ := b0e16 (M.op X1 X2) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X0 (M.op X1 X2))
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 (M.op X1 X2) X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e108 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e120 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e40 X0
           have i₂ := b0e40 X1
           grind)
        | exact superpose b0e40 b0e40
        | exact resolve b0e40 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e206 : (M.op y x) = (k (M.op y x) (M.op y x)) := by grind
      clear b0e56
      have b0e349 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e120 (σ x) X0
           grind)
        | (have i₁ := b0e18
           have i₂ := b0e120 X0 (σ x)
           grind)
        | exact superpose b0e120 b0e18
        | exact resolve b0e18 b0e120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e120
      have b0e861 : ∀ X0 X1 : G, (M.op X1 (σ y)) ≠ (σ (M.op X0 y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e349 X1
           have i₂ := b0e48 x X0
           grind)
        | (have i₁ := b0e349 X1
           have i₂ := b0e48 X0 x
           grind)
        | exact superpose b0e48 b0e349
        | exact resolve b0e349 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e349
      have b0e1550 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have j0 := b0e96 X0 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96
      have b0e1583 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y x)) := by
        intro X0
        first
        | (have i₁ := b0e861 x X0
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e861
        | exact resolve b0e861 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e861
      have b0e1688 : ∀ X0 X1 : G, (M.op X0 (σ y)) ≠ (M.op (σ y) (σ x)) ∨ (M.op X0 (σ y)) = (M.op X1 X1) ∨ (k X1 (M.op X0 (σ y))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e57 (σ y) X0 X1
           have i₂ := b0e40 (M.op (σ y) X0)
           grind)
        | exact superpose b0e40 b0e57
        | (have j0 := b0e57 (σ y) X0 X1
           grind)
        | exact resolve b0e57 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57
      have b0e1698 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 X1) ∨ (k X1 (M.op X0 (σ y))) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e1688 X0 X1
           grind)
        | (have r₁ := b0e1688 X0 X1
           have r₂ := b0e40 X0
           grind)
        | exact resolve b0e1688 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1688
      have b0e1969 : ∀ X0 : G, (k y X0) = (M.op y X0) ∨ (M.op y x) = X0 ∨ (M.op y X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e97 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e97
        | exact resolve b0e97 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e97
      have b0e2171 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ X1) (σ X0)) (σ X1)) = (M.op X2 (M.op X3 (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e43 (σ X1) (σ X0) X2 X3
           have i₂ := b0e90 X0 X1
           grind)
        | exact superpose b0e90 b0e43
        | (have j1 := b0e90 X0 X1
           grind)
        | exact resolve b0e43 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e2217 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e90 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e2219 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e2217 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2217
      have b0e23218 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by
        first
        | (have i₁ := b0e2219 (M.op y x)
           have i₂ := b0e206
           grind)
        | exact superpose b0e206 b0e2219
        | (have j0 := b0e2219 (M.op y x)
           grind)
        | exact resolve b0e2219 b0e206
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e206 b0e2219
      have b0e23229 : (σ (M.op y x)) = (M.op (σ (M.op y x)) (σ (M.op y x))) := by grind
      clear b0e23218
      have b0e26122 : ∀ X0 X1 : G, (k X1 (M.op X0 (σ y))) = X1 ∨ (k X1 (M.op X0 (σ y))) = X1 := by
        intro X0 X1
        grind
      clear b0e1698
      have b0e26274 : ∀ X0 X1 : G, (k X1 (M.op X0 (σ y))) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e26122 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26122
      have b0e26348 : ∀ X0 : G, (k X0 (M.op (σ y) (σ x))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e26274 x X0
           have i₂ := b0e40 x
           grind)
        | exact superpose b0e40 b0e26274
        | exact resolve b0e26274 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e26274
      have b0e27799 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ y) (σ x)))) := by
        intro X0
        first
        | (have i₁ := b0e108 X0 (M.op (σ y) (σ x))
           have i₂ := b0e26348 (σ X0)
           grind)
        | exact superpose b0e26348 b0e108
        | exact resolve b0e108 b0e26348
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e108 b0e26348
      have b0e27804 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ x)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e27799 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e27799
        | exact resolve b0e27799 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27799
      have b0e58436 : y ≠ (M.op y x) ∨ (M.op y y) = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e1550 y x
           have i₂ := b0e41 x
           grind)
        | exact superpose b0e41 b0e1550
        | (have j0 := b0e1550 y x
           grind)
        | exact resolve b0e1550 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1550
      have b0e58530 : (M.op y y) = (k y y) ∨ y = (M.op y y) := by
        first
        | (have j1 := b0e1969 y
           grind)
        | (have r₁ := b0e58436
           have r₂ := b0e1969 y
           grind)
        | exact resolve b0e58436 b0e1969
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1969 b0e58436
      have b0e58573 : (M.op y x) = (k y y) ∨ y = (M.op y y) := by
        first
        | (have i₁ := b0e58530
           have i₂ := b0e41 y
           grind)
        | exact superpose b0e41 b0e58530
        | exact resolve b0e58530 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58530
      have b0e58603 : (M.op y x) = (k y y) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e58573
           have i₂ := b0e41 y
           grind)
        | exact superpose b0e41 b0e58573
        | exact resolve b0e58573 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e58573
      have b0e294061 : ∀ X0 X1 : G, (M.op X0 (σ (M.op y x))) = (M.op X1 (σ (M.op y x))) := by
        intro X0 X1
        first
        | (have i₁ := b0e42 X0 (σ (M.op y x)) (σ (M.op y x)) x
           have i₂ := b0e23229
           grind)
        | exact superpose b0e23229 b0e42
        | exact resolve b0e42 b0e23229
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42
      have b0e368063 : ∀ X0 : G, (σ (M.op y x)) = (M.op X0 (σ (M.op y x))) := by
        intro X0
        first
        | (have i₁ := b0e23229
           have i₂ := b0e294061 (σ (M.op y x)) X0
           grind)
        | (have i₁ := b0e23229
           have i₂ := b0e294061 X0 (σ (M.op y x))
           grind)
        | exact superpose b0e294061 b0e23229
        | exact resolve b0e23229 b0e294061
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23229 b0e294061
      have b0e400474 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (M.op X1 (σ (M.op y x)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
        intro X0 X1
        first
        | (have i₁ := b0e2171 y y X0 X1
           have i₂ := b0e58603
           grind)
        | exact superpose b0e58603 b0e2171
        | (have j0 := b0e2171 y y x x
           grind)
        | exact resolve b0e2171 b0e58603
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2171
      have b0e403045 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (M.op X1 (σ (M.op y x)))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
        intro X0 X1
        first
        | (have j0 := b0e400474 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e400474
      have b0e403656 : ∀ X0 : G, (M.op (M.op (σ y) (σ y)) (σ y)) = (M.op X0 (σ (M.op y x))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e403045 X0 x
           have i₂ := b0e368063 x
           grind)
        | exact superpose b0e368063 b0e403045
        | exact resolve b0e403045 b0e368063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e403045
      have b0e403965 : (σ (M.op y x)) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e403656 x
           have i₂ := b0e368063 x
           grind)
        | exact superpose b0e368063 b0e403656
        | exact resolve b0e403656 b0e368063
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e403656
      have b0e404102 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by
        first
        | (have r₁ := b0e403965
           have r₂ := b0e1583 (M.op (σ y) (σ y))
           grind)
        | exact resolve b0e403965 b0e1583
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e403965
      have b0e404191 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e404102
           have i₂ := b0e40 (σ y)
           grind)
        | exact superpose b0e40 b0e404102
        | exact resolve b0e404102 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e404102
      have b0e404322 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ y = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e27804 X0
           have i₂ := b0e404191
           grind)
        | exact superpose b0e404191 b0e27804
        | exact resolve b0e27804 b0e404191
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27804 b0e404191
      have b0e404732 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op y x) := by
        intro X0
        first
        | (have i₁ := b0e404322 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e404322
        | exact resolve b0e404322 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e404322
      have b0e406513 : y = (M.op y x) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
        first
        | (have i₁ := b0e58603
           have i₂ := b0e404732 y
           grind)
        | exact superpose b0e404732 b0e58603
        | exact resolve b0e58603 b0e404732
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58603 b0e404732
      have b0e406520 : y = (M.op y x) := by grind
      clear b0e406513
      have b0e409170 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e1583 X0
           have i₂ := b0e406520
           grind)
        | exact superpose b0e406520 b0e1583
        | exact resolve b0e1583 b0e406520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1583
      have b0e409222 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e368063 X0
           have i₂ := b0e406520
           grind)
        | exact superpose b0e406520 b0e368063
        | exact resolve b0e368063 b0e406520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e368063 b0e406520
      have b0e409565 : False := by grind
      exact b0e409565
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
        have b1e36 : ∀ X0 : G, (M.op X0 y) = (M.op y x) := by
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
        have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b1e12 X0 X1 X2
             have i₂ := b1e12 X3 X1 X2
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e36 X0
             have i₂ := b1e36 X1
             grind)
          | exact superpose b1e36 b1e36
          | exact resolve b1e36 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e84 : ∀ X0 : G, (σ y) ≠ (σ (M.op X0 y)) := by
          intro X0
          first
          | (have i₁ := b1e24
             have i₂ := b1e43 x X0
             grind)
          | (have i₁ := b1e24
             have i₂ := b1e43 X0 x
             grind)
          | exact superpose b1e43 b1e24
          | exact resolve b1e24 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e43
        have b1e125 : (σ y) ≠ (σ (M.op y x)) := by
          first
          | (have i₁ := b1e84 x
             have i₂ := b1e36 x
             grind)
          | exact superpose b1e36 b1e84
          | exact resolve b1e84 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e141 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b1e37 X0 (σ x) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e37
          | exact resolve b1e37 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e382 : ∀ X0 : G, (σ y) = (k (σ y) (M.op X0 (σ y))) := by
          intro X0
          grind
        have b1e391 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e22
             have i₂ := b1e141 (σ x) X0
             grind)
          | (have i₁ := b1e22
             have i₂ := b1e141 X0 (σ x)
             grind)
          | exact superpose b1e141 b1e22
          | exact resolve b1e22 b1e141
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e141
        have b1e398 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e382 x
             have i₂ := b1e391 x
             grind)
          | exact superpose b1e391 b1e382
          | exact resolve b1e382 b1e391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e382 b1e391
        have b1e414 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b1e398
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e398
          | exact resolve b1e398 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e398
        have b1e630 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b1e414
             have i₂ := b1e17 y y
             grind)
          | exact superpose b1e17 b1e414
          | (have j1 := b1e17 y y
             grind)
          | exact resolve b1e414 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e414
        have b1e634 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b1e630
        have b1e638 : y = (M.op y y) := by
          first
          | (have r₁ := b1e634
             have r₂ := b1e84 y
             grind)
          | exact resolve b1e634 b1e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e84 b1e634
        have b1e639 : y = (M.op y x) := by
          first
          | (have i₁ := b1e638
             have i₂ := b1e36 y
             grind)
          | exact superpose b1e36 b1e638
          | exact resolve b1e638 b1e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36 b1e638
        have b1e1208 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e125
             have i₂ := b1e639
             grind)
          | exact superpose b1e639 b1e125
          | exact resolve b1e125 b1e639
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e125 b1e639
        have b1e1223 : False := by grind
        exact b1e1223
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
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
        have b2e34 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X0 X1 X2
             have i₂ := b2e12 X3 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e87 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
        have b2e111 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e1496 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e1497 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1496
             have r₂ := b2e22
             grind)
          | exact resolve b2e1496 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1496
        have b2e1498 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1497
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1497
          | exact resolve b2e1497 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1497
        have b2e1499 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1498
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1498
          | exact resolve b2e1498 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1498
        have b2e1503 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1499
             grind)
          | exact superpose b2e1499 b2e22
          | exact resolve b2e22 b2e1499
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1511 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) := by
          intro X0 X1
          first
          | (have i₁ := b2e34 X0 (σ x) (σ y) x
             have i₂ := b2e1499
             grind)
          | exact superpose b2e1499 b2e34
          | exact resolve b2e34 b2e1499
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e1499
        have b2e1918 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e81 x x
             grind)
          | exact superpose b2e81 b2e21
          | (have j1 := b2e81 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e81 x y
             grind)
          | exact resolve b2e21 b2e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e81
        have b2e1979 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e1918
        have b2e2198 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e111
        have b2e2215 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e2198 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e2198
          | exact resolve b2e2198 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2198
        have b2e3113 : ∀ X0 : G, x = (k x (τ (M.op X0 (σ x)))) := by
          intro X0
          first
          | (have i₁ := b2e2215 x
             have i₂ := b2e1511 (σ x) X0
             grind)
          | (have i₁ := b2e2215 x
             have i₂ := b2e1511 X0 (σ x)
             grind)
          | exact superpose b2e1511 b2e2215
          | exact resolve b2e2215 b2e1511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1511 b2e2215
        have b2e15817 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1979
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e1979
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e1979 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1979
        have b2e15818 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15817
        have b2e15820 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e15818
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15818
          | exact resolve b2e15818 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15818
        have b2e15821 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e15820
        have b2e15829 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e15821
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15821
          | exact resolve b2e15821 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15821
        have b2e15853 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e3113 (σ x)
             have i₂ := b2e15829
             grind)
          | exact superpose b2e15829 b2e3113
          | exact resolve b2e3113 b2e15829
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3113 b2e15829
        have b2e15905 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e15853
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e15853
          | exact resolve b2e15853 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15853
        have b2e16953 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e15905
             grind)
          | exact superpose b2e15905 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e15905
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e15905
        have b2e16954 : x = (M.op x x) ∨ x = y := by grind
        clear b2e16953
        have b2e16967 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e16954
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16954
          | exact resolve b2e16954 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e16954
        have b2e16968 : x = y := by grind
        clear b2e16967
        have b2e18511 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e1503
             have i₂ := b2e16968
             grind)
          | exact superpose b2e16968 b2e1503
          | exact resolve b2e1503 b2e16968
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1503 b2e16968
        have b2e18525 : False := by grind
        exact b2e18525
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
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
        have b3e48 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e128 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b3e203 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e48 X0
             have i₂ := b3e48 X1
             grind)
          | exact superpose b3e48 b3e48
          | exact resolve b3e48 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e243 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e24
             have i₂ := b3e203 (σ x) X0
             grind)
          | (have i₁ := b3e24
             have i₂ := b3e203 X0 (σ x)
             grind)
          | exact superpose b3e203 b3e24
          | exact resolve b3e24 b3e203
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e203
        have b3e299 : (σ y) ≠ (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b3e243 x
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e243
          | exact resolve b3e243 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e243
        have b3e2140 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e128 x x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e128
          | exact resolve b3e128 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e2244 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b3e2140
        have b3e2948 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e13 (k x x)
             have i₂ := b3e2244
             grind)
          | exact superpose b3e2244 b3e13
          | exact resolve b3e13 b3e2244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e2964 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2948
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e2948
          | exact resolve b3e2948 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2948
        have b3e3503 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e17 x x
             have i₂ := b3e2964
             grind)
          | exact superpose b3e2964 b3e17
          | (have j0 := b3e17 x x
             grind)
          | exact resolve b3e17 b3e2964
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2964
        have b3e3504 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b3e3503
        have b3e3506 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b3e3504
             have r₂ := b3e20
             grind)
          | exact resolve b3e3504 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3504
        have b3e3602 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b3e3506
        have b3e4054 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e2244
             have i₂ := b3e3602
             grind)
          | exact superpose b3e3602 b3e2244
          | exact resolve b3e2244 b3e3602
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2244 b3e3602
        have b3e4063 : (σ x) = (σ y) := by grind
        clear b3e4054
        have b3e4260 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e299
             have i₂ := b3e4063
             grind)
          | exact superpose b3e4063 b3e299
          | exact resolve b3e299 b3e4063
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e299
        have b3e4286 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e4260
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e4260
          | exact resolve b3e4260 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4260
        have b3e4295 : False := by grind
        exact b3e4295
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
            intro X0 X1 X2
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e35 : ∀ X0 : G, (M.op (M.op y x) y) = (M.op X0 y) := by
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
          have b5e42 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e13 X3 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 X1 : G, (M.op X0 y) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 X1
               have i₂ := b5e35 X0
               grind)
            | (have i₁ := b5e35 X0
               have i₂ := b5e35 (M.op y x)
               grind)
            | exact superpose b5e35 b5e35
            | exact resolve b5e35 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e105 : ∀ X0 : G, y = (k y (M.op X0 y)) := by
            intro X0
            grind
          have b5e111 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e22
               have i₂ := b5e47 x X0
               grind)
            | (have i₁ := b5e22
               have i₂ := b5e47 X0 x
               grind)
            | exact superpose b5e47 b5e22
            | exact resolve b5e22 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e116 : y = (k y y) := by
            first
            | (have i₁ := b5e105 x
               have i₂ := b5e111 x
               grind)
            | exact superpose b5e111 b5e105
            | exact resolve b5e105 b5e111
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e105 b5e111
          have b5e1719 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e75 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e75
          have b5e1721 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b5e1719 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1719
          have b5e9536 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b5e1721 y
               have i₂ := b5e116
               grind)
            | exact superpose b5e116 b5e1721
            | (have j0 := b5e1721 y
               grind)
            | exact resolve b5e1721 b5e116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e116 b5e1721
          have b5e9540 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b5e9536
          have b5e9603 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e42 X0 (σ y) (σ y) x
               have i₂ := b5e9540
               grind)
            | exact superpose b5e9540 b5e42
            | exact resolve b5e42 b5e9540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e9907 : ∀ X0 : G, (σ y) ≠ (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e9603 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e9603 X0 (σ x)
               grind)
            | exact superpose b5e9603 b5e24
            | exact resolve b5e24 b5e9603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e9911 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e9540
               have i₂ := b5e9603 (σ y) X0
               grind)
            | (have i₁ := b5e9540
               have i₂ := b5e9603 X0 (σ y)
               grind)
            | exact superpose b5e9603 b5e9540
            | exact resolve b5e9540 b5e9603
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e9540 b5e9603
          have b5e9917 : False := by grind
          exact b5e9917
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
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
        have b6e85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e87 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
        have b6e97 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e87
             have r₂ := b6e20
             grind)
          | exact resolve b6e87 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e87
        have b6e100 : x = (M.op x y) := by
          first
          | (have r₁ := b6e97
             have r₂ := b6e21
             grind)
          | exact resolve b6e97 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e97
        have b6e102 : x ≠ y := by
          first
          | (have i₁ := b6e21
             have i₂ := b6e100
             grind)
          | exact superpose b6e100 b6e21
          | exact resolve b6e21 b6e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e100
        have b6e1481 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e85 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e85
          | exact resolve b6e85 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e85
        have b6e1577 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1481
        have b6e2270 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1577
             grind)
          | exact superpose b6e1577 b6e13
          | exact resolve b6e13 b6e1577
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e2285 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2270
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2270
          | exact resolve b6e2270 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2270
        have b6e3443 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e2285
             grind)
          | exact superpose b6e2285 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e2285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2285
        have b6e3444 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3443
        have b6e3446 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e3444
             have r₂ := b6e20
             grind)
          | exact resolve b6e3444 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3444
        have b6e3514 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e3446
        have b6e3735 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1577
             have i₂ := b6e3514
             grind)
          | exact superpose b6e3514 b6e1577
          | exact resolve b6e1577 b6e3514
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1577 b6e3514
        have b6e3744 : (σ x) = (σ y) := by grind
        clear b6e3735
        have b6e3831 : y = (τ (σ x)) := by
          first
          | (have i₁ := b6e13 y
             have i₂ := b6e3744
             grind)
          | exact superpose b6e3744 b6e13
          | exact resolve b6e13 b6e3744
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3744
        have b6e3859 : x = y := by
          first
          | (have i₁ := b6e3831
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e3831
          | exact resolve b6e3831 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3831
        have b6e3869 : False := by grind
        exact b6e3869
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X1) X2) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X0) X3) (M.op X1 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X3 (M.op X1 X0)
               have i₂ := b7e13 X3 X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X1 X2
               have i₂ := b7e13 X3 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op (M.op X0 X1) X0)) := by
            intro X0 X1
            grind
          have b7e40 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e30 X0 X1 X2 x
               have i₂ := b7e13 (M.op (M.op X1 X0) x) X1 X0
               grind)
            | exact superpose b7e13 b7e30
            | exact resolve b7e30 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30
          have b7e104 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 X0 (σ x) (σ y) x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e36
            | exact resolve b7e36 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e872 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (M.op X0 (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b7e38 (σ y) X1
               have i₂ := b7e104 (M.op (σ y) X1) X0
               grind)
            | (have i₁ := b7e38 (σ y) X1
               have i₂ := b7e104 X0 (M.op (σ y) X1)
               grind)
            | exact superpose b7e104 b7e38
            | exact resolve b7e38 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38
          have b7e877 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e24
               have i₂ := b7e104 (σ x) X0
               grind)
            | (have i₁ := b7e24
               have i₂ := b7e104 X0 (σ x)
               grind)
            | exact superpose b7e104 b7e24
            | exact resolve b7e24 b7e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e104
          have b7e882 : ∀ X1 : G, (M.op X1 (σ y)) = (k (M.op X1 (σ y)) (σ y)) := by
            intro X1
            first
            | (have i₁ := b7e872 x X1
               have i₂ := b7e877 x
               grind)
            | exact superpose b7e877 b7e872
            | exact resolve b7e872 b7e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e872
          have b7e922 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e882 x
               have i₂ := b7e877 x
               grind)
            | exact superpose b7e877 b7e882
            | exact resolve b7e882 b7e877
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e877 b7e882
          have b7e940 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b7e922
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e922
            | exact resolve b7e922 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e922
          have b7e1189 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k y y)
               have i₂ := b7e940
               grind)
            | exact superpose b7e940 b7e14
            | exact resolve b7e14 b7e940
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e940
          have b7e1191 : y = (k y y) := by
            first
            | (have i₁ := b7e1189
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e1189
            | exact resolve b7e1189 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1189
          have b7e1199 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b7e18 y y
               have i₂ := b7e1191
               grind)
            | exact superpose b7e1191 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e1191
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1191
          have b7e1200 : y = (M.op y y) := by grind
          clear b7e1199
          have b7e1294 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b7e40 y y x
               have i₂ := b7e1200
               grind)
            | exact superpose b7e1200 b7e40
            | exact resolve b7e40 b7e1200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e40
          have b7e1297 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b7e1294 X0
               have i₂ := b7e1200
               grind)
            | exact superpose b7e1200 b7e1294
            | exact resolve b7e1294 b7e1200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1200 b7e1294
          have b7e1423 : y ≠ y := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e1297 x
               grind)
            | exact superpose b7e1297 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e1297 x
               grind)
            | exact resolve b7e22 b7e1297
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1297
          have b7e1424 : False := by grind
          exact b7e1424
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
          have b8e66 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op (σ x) X0) = X0 := by
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
          have b8e1120 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have j0 := b8e66 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e1121 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1120
               have r₂ := b8e24
               grind)
            | exact resolve b8e1120 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1120
          have b8e1122 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1121
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1121
            | exact resolve b8e1121 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1121
          have b8e1125 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1122
               grind)
            | exact superpose b8e1122 b8e20
            | exact resolve b8e20 b8e1122
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1122
          have b8e1405 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1125
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1125
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1125 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1125
          have b8e1406 : y = (M.op x x) ∨ y = (M.op x y) := by grind
          clear b8e1405
          have b8e1409 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1406
               have r₂ := b8e21
               grind)
            | exact resolve b8e1406 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1406
          have b8e1412 : False := by grind
          exact b8e1412

/-- `Equation677`: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op y x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
      have b0e28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k (τ X0) X1)
           have i₂ := b0e21 X0 X1
           grind)
        | exact superpose b0e21 b0e12
        | exact resolve b0e12 b0e21
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e22 X1 X0
           grind)
        | exact superpose b0e22 b0e12
        | exact resolve b0e12 b0e22
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e46 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e40 (σ X0)
           grind)
        | exact superpose b0e40 b0e17
        | exact resolve b0e17 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e48 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e40 (τ X0)
           grind)
        | exact superpose b0e40 b0e22
        | exact resolve b0e22 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e48 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e48
        | exact resolve b0e48 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48
      have b0e51 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e46
        | exact resolve b0e46 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e53 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e40 X0
           grind)
        | exact superpose b0e40 b0e49
        | exact resolve b0e49 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40 b0e49
      have b0e69 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X1
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e15 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e16 X1 X0
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e16 X0 X0
           grind)
        | (have r₁ := b0e15 X1 X1
           have r₂ := b0e16 X1 X1
           grind)
        | (have r₁ := b0e15 X0 X1
           have r₂ := b0e16 X0 X1
           grind)
        | exact resolve b0e15 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
      have b0e81 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e84 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e69 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e77 X0 X1
           have i₂ := b0e51 X1
           grind)
        | exact superpose b0e51 b0e77
        | (have j0 := b0e77 X0 X1
           grind)
        | exact resolve b0e77 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e90 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e84 X0 X1
           have j1 := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X0 X1
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X1 X0
           have r₂ := b0e81 X0 X1
           grind)
        | (have r₁ := b0e84 X1 X1
           have r₂ := b0e81 X1 X1
           grind)
        | exact resolve b0e84 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81 b0e84
      have b0e93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e88 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e88
        | (have j0 := b0e88 X0 X1
           grind)
        | exact resolve b0e88 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88
      have b0e107 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e188 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e14
        | (have j0 := b0e14 (σ X0) X1
           grind)
        | exact resolve b0e14 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e210 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e12 (M.op (τ X0) (τ X0))
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e12
        | exact resolve b0e12 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e334 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (τ X0) X1
           have i₂ := b0e210 X0
           grind)
        | exact superpose b0e210 b0e14
        | (have j0 := b0e14 (τ X0) X1
           grind)
        | exact resolve b0e14 b0e210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e387 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X0 X1
           have i₂ := b0e90 X1 (τ X0)
           grind)
        | exact superpose b0e90 b0e21
        | (have j1 := b0e90 X1 (τ X0)
           grind)
        | exact resolve b0e21 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21
      have b0e390 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e90 (τ X0) X1
           grind)
        | exact superpose b0e90 b0e22
        | (have j1 := b0e90 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e90
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90
      have b0e410 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e387 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e387
        | (have j0 := b0e387 X0 X1
           grind)
        | exact resolve b0e387 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e387
      have b0e430 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e410 X0 X1
           have i₂ := b0e210 X0
           grind)
        | exact superpose b0e210 b0e410
        | (have j0 := b0e410 X0 X1
           grind)
        | exact resolve b0e410 b0e210
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e210 b0e410
      have b0e1392 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (σ X0) (σ X1)
           have i₂ := b0e93 X1 X0
           grind)
        | exact superpose b0e93 b0e14
        | (have j0 := b0e14 (σ X0) (σ X1)
           have j1 := b0e93 X1 X0
           grind)
        | exact resolve b0e14 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1425 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1426 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1427 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e93 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93
      have b0e1472 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e1392 X0 X1
           have j1 := b0e188 X0 (σ X1)
           grind)
        | (have r₁ := b0e1392 X0 X0
           have r₂ := b0e188 X0 (σ X0)
           grind)
        | (have r₁ := b0e1392 X0 X1
           have r₂ := b0e188 X0 (σ X1)
           grind)
        | exact resolve b0e1392 b0e188
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e188 b0e1392
      have b0e1526 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1472 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e1472
        | (have j0 := b0e1472 X0 X1
           grind)
        | exact resolve b0e1472 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1472
      have b0e1562 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1526 X0 X1
           have i₂ := b0e51 X1
           grind)
        | exact superpose b0e51 b0e1526
        | (have j0 := b0e1526 X0 X1
           grind)
        | exact resolve b0e1526 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1526
      have b0e1584 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e1562 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e1562
        | (have j0 := b0e1562 X0 X1
           grind)
        | exact resolve b0e1562 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1562
      have b0e7392 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e390 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e390
        | exact resolve b0e390 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e390
      have b0e7620 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e7392 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e7392
        | (have j0 := b0e7392 X0 X1
           grind)
        | exact resolve b0e7392 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7392
      have b0e8071 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e334 X0 X1
           have i₂ := b0e430 X0 X1
           grind)
        | exact superpose b0e430 b0e334
        | (have j0 := b0e334 X0 X1
           have j1 := b0e430 X0 X1
           grind)
        | (have r₁ := b0e334 X0 X1
           have r₂ := b0e430 X0 X1
           grind)
        | exact resolve b0e334 b0e430
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e334 b0e430
      have b0e8253 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e8071 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8071
      have b0e12855 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1584 (τ X1) (τ X0)
           have i₂ := b0e107 X0 X1
           grind)
        | exact superpose b0e107 b0e1584
        | (have j0 := b0e1584 (τ X0) (τ X1)
           grind)
        | exact resolve b0e1584 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1584
      have b0e12949 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12855 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e12855
        | (have j0 := b0e12855 X0 X1
           grind)
        | exact resolve b0e12855 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12855
      have b0e12986 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12949 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e12949
        | (have j0 := b0e12949 X0 X1
           grind)
        | exact resolve b0e12949 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12949
      have b0e13013 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e12986 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e12986
        | (have j0 := b0e12986 X0 X1
           grind)
        | exact resolve b0e12986 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e12986
      have b0e13033 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e13013 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e13013
        | (have j0 := b0e13013 X0 X1
           grind)
        | exact resolve b0e13013 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13013
      have b0e13045 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13033 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e13033
        | (have j0 := b0e13033 X0 X1
           grind)
        | exact resolve b0e13033 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13033
      have b0e13053 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13045 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e13045
        | (have j0 := b0e13045 X0 X1
           grind)
        | exact resolve b0e13045 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13045
      have b0e13057 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13053 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e13053
        | (have j0 := b0e13053 X0 X1
           grind)
        | exact resolve b0e13053 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13053
      have b0e20543 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1426 (τ X1) (τ X0)
           have i₂ := b0e107 X1 X0
           grind)
        | exact superpose b0e107 b0e1426
        | (have j0 := b0e1426 (τ X1) (τ X0)
           grind)
        | exact resolve b0e1426 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1426
      have b0e20663 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20543 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e20543
        | (have j0 := b0e20543 X0 X1
           grind)
        | exact resolve b0e20543 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20543
      have b0e20713 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20663 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e20663
        | (have j0 := b0e20663 X0 X1
           grind)
        | exact resolve b0e20663 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20663
      have b0e20751 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20713 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e20713
        | (have j0 := b0e20713 X0 X1
           grind)
        | exact resolve b0e20713 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20713
      have b0e20780 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20751 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e20751
        | (have j0 := b0e20751 X0 X1
           grind)
        | exact resolve b0e20751 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20751
      have b0e20805 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e20780 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e20780
        | (have j0 := b0e20780 X0 X1
           grind)
        | exact resolve b0e20780 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20780
      have b0e20828 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e20805 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e20805
        | (have j0 := b0e20805 X0 X1
           grind)
        | exact resolve b0e20805 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20805
      have b0e20845 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e20828 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e20828
        | (have j0 := b0e20828 X0 X1
           grind)
        | exact resolve b0e20828 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20828
      have b0e20858 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e20845 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e20845
        | (have j0 := b0e20845 X0 X1
           grind)
        | exact resolve b0e20845 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20845
      have b0e21042 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e1427 (τ X1) (τ X0)
           have i₂ := b0e107 X1 X0
           grind)
        | exact superpose b0e107 b0e1427
        | (have j0 := b0e1427 (τ X1) (τ X0)
           grind)
        | exact resolve b0e1427 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1427
      have b0e21160 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e21042 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e21042
        | (have j0 := b0e21042 X0 X1
           grind)
        | exact resolve b0e21042 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21042
      have b0e21207 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e21160 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e21160
        | (have j0 := b0e21160 X0 X1
           grind)
        | exact resolve b0e21160 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21160
      have b0e21244 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e21207 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e21207
        | (have j0 := b0e21207 X0 X1
           grind)
        | exact resolve b0e21207 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21207
      have b0e21273 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e21244 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e21244
        | (have j0 := b0e21244 X0 X1
           grind)
        | exact resolve b0e21244 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21244
      have b0e21298 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e21273 X0 X1
           have i₂ := b0e53 X1
           grind)
        | exact superpose b0e53 b0e21273
        | (have j0 := b0e21273 X0 X1
           grind)
        | exact resolve b0e21273 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21273
      have b0e21319 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e21298 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e21298
        | (have j0 := b0e21298 X0 X1
           grind)
        | exact resolve b0e21298 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21298
      have b0e21336 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e21319 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e21319
        | (have j0 := b0e21319 X0 X1
           grind)
        | exact resolve b0e21319 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21319
      have b0e21349 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e21336 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e21336
        | (have j0 := b0e21336 X0 X1
           grind)
        | exact resolve b0e21336 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21336
      have b0e70521 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 (τ X1)
           have i₂ := b0e8253 X1 (τ X0)
           grind)
        | exact superpose b0e8253 b0e22
        | (have j1 := b0e8253 X1 (τ X0)
           grind)
        | exact resolve b0e22 b0e8253
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22
      have b0e70854 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 (σ X1)
           have i₂ := b0e8253 (σ X0) X1
           grind)
        | exact superpose b0e8253 b0e35
        | (have j1 := b0e8253 (σ X0) X1
           grind)
        | exact resolve b0e35 b0e8253
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8253
      have b0e71255 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e70854 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e70854
        | (have j0 := b0e70854 X0 X1
           grind)
        | exact resolve b0e70854 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70854
      have b0e71395 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e70521 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e70521
        | (have j0 := b0e70521 X0 X1
           grind)
        | exact resolve b0e70521 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70521
      have b0e71726 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e71255 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e71255
        | (have j0 := b0e71255 X0 X1
           grind)
        | exact resolve b0e71255 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71255
      have b0e71800 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e71395 X0 X1
           have i₂ := b0e53 X0
           grind)
        | exact superpose b0e53 b0e71395
        | (have j0 := b0e71395 X0 X1
           grind)
        | exact resolve b0e71395 b0e53
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e71395
      have b0e72012 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e71726 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e71726
        | (have j0 := b0e71726 X0 X1
           grind)
        | exact resolve b0e71726 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71726
      have b0e72065 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e71800 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e71800
        | (have j0 := b0e71800 X0 X1
           grind)
        | exact resolve b0e71800 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71800
      have b0e72204 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e72012 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e72012
        | (have j0 := b0e72012 X0 X1
           grind)
        | exact resolve b0e72012 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72012
      have b0e72247 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e72065 X0 X1
           have i₂ := b0e107 X0 X1
           grind)
        | exact superpose b0e107 b0e72065
        | (have j0 := b0e72065 X0 X1
           grind)
        | exact resolve b0e72065 b0e107
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e107 b0e72065
      have b0e72305 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e72204 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e72204
        | (have j0 := b0e72204 X0 X1
           grind)
        | exact resolve b0e72204 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72204
      have b0e76728 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 X1
           have i₂ := b0e72305 (σ X0) X1
           grind)
        | exact superpose b0e72305 b0e35
        | (have j1 := b0e72305 (σ X0) X1
           grind)
        | exact resolve b0e35 b0e72305
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72305
      have b0e77080 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e76728 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e76728
        | (have j0 := b0e76728 X0 X1
           grind)
        | exact resolve b0e76728 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76728
      have b0e77769 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e77080 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e77080
        | (have j0 := b0e77080 X0 X1
           grind)
        | exact resolve b0e77080 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77080
      have b0e88731 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e13057 X1 X0
           have i₂ := b0e72247 X0 X1
           grind)
        | exact superpose b0e72247 b0e13057
        | (have j0 := b0e13057 X0 X1
           have j1 := b0e72247 X1 X0
           grind)
        | (have r₁ := b0e13057 X1 X0
           have r₂ := b0e72247 X0 X1
           grind)
        | (have r₁ := b0e13057 X1 X1
           have r₂ := b0e72247 X1 X1
           grind)
        | exact resolve b0e13057 b0e72247
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e89224 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e20858 X1 X0
           have i₂ := b0e72247 X0 X1
           grind)
        | exact superpose b0e72247 b0e20858
        | (have j0 := b0e20858 X1 X0
           have j1 := b0e72247 X0 X1
           grind)
        | (have r₁ := b0e20858 X1 X1
           have r₂ := b0e72247 X1 X1
           grind)
        | (have r₁ := b0e20858 X1 X0
           have r₂ := b0e72247 X0 X1
           grind)
        | exact resolve b0e20858 b0e72247
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20858
      have b0e89406 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e72247 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e89407 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e72247 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e72247
      have b0e89411 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e89224 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89224
      have b0e89462 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e88731 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e88731
      have b0e89965 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e89411 X0 X1
           have j1 := b0e21349 X1 X0
           grind)
        | (have r₁ := b0e89411 X1 X0
           have r₂ := b0e21349 X0 X1
           grind)
        | exact resolve b0e89411 b0e21349
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21349 b0e89411
      have b0e90239 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e89462 X0 X1
           have j1 := b0e89406 X0 X1
           grind)
        | (have r₁ := b0e89462 X0 X1
           have r₂ := b0e89406 X0 X1
           grind)
        | (have r₁ := b0e89462 X1 X0
           have r₂ := b0e89406 X0 X1
           grind)
        | (have r₁ := b0e89462 X1 X1
           have r₂ := b0e89406 X1 X1
           grind)
        | exact resolve b0e89462 b0e89406
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89406 b0e89462
      have b0e124606 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e89965 X0 X1
           grind)
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e89965 X0 X1
           grind)
        | exact superpose b0e89965 b0e15
        | (have j0 := b0e15 X1 X0
           have j1 := b0e89965 X0 X1
           grind)
        | (have r₁ := b0e15 X1 X1
           have r₂ := b0e89965 X1 X1
           grind)
        | (have r₁ := b0e15 X1 X0
           have r₂ := b0e89965 X0 X1
           grind)
        | (have r₁ := b0e15 X0 X0
           have r₂ := b0e89965 X0 X0
           grind)
        | exact resolve b0e15 b0e89965
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89965
      have b0e125278 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e124606 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124606
      have b0e125476 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e125278 X0 X1
           have j1 := b0e89407 X1 X0
           grind)
        | (have r₁ := b0e125278 X0 X1
           have r₂ := b0e89407 X0 X1
           grind)
        | (have r₁ := b0e125278 X1 X0
           have r₂ := b0e89407 X0 X1
           grind)
        | (have r₁ := b0e125278 X1 X1
           have r₂ := b0e89407 X1 X1
           grind)
        | exact resolve b0e125278 b0e89407
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e89407 b0e125278
      have b0e126516 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e90239 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e90239
        | (have j0 := b0e90239 (σ X0) X1
           grind)
        | exact resolve b0e90239 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e90239
      have b0e128026 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e126516 X0 X1
           have i₂ := b0e35 X0 X1
           grind)
        | exact superpose b0e35 b0e126516
        | (have j0 := b0e126516 X0 X1
           grind)
        | exact resolve b0e126516 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e126516
      have b0e155742 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e125476 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e125476
        | (have j0 := b0e125476 (σ X0) X1
           grind)
        | exact resolve b0e125476 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125476
      have b0e157475 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e155742 X0 X1
           have i₂ := b0e28 X1 X0
           grind)
        | exact superpose b0e28 b0e155742
        | (have j0 := b0e155742 X0 X1
           grind)
        | exact resolve b0e155742 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e155742
      have b0e179738 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (σ X1) X0
           have i₂ := b0e77769 X1 (σ X0)
           grind)
        | exact superpose b0e77769 b0e28
        | (have j1 := b0e77769 X1 (σ X0)
           grind)
        | exact resolve b0e28 b0e77769
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77769
      have b0e179749 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179738 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e179738
        | (have j0 := b0e179738 X0 X1
           grind)
        | exact resolve b0e179738 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179738
      have b0e179787 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179749 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e179749
        | (have j0 := b0e179749 X0 X1
           grind)
        | exact resolve b0e179749 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179749
      have b0e179817 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179787 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e179787
        | (have j0 := b0e179787 X0 X1
           grind)
        | exact resolve b0e179787 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179787
      have b0e179838 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e179817 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e179817
        | (have j0 := b0e179817 X0 X1
           grind)
        | exact resolve b0e179817 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179817
      have b0e179850 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e179838 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e179838
        | (have j0 := b0e179838 X0 X1
           grind)
        | exact resolve b0e179838 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179838
      have b0e186178 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e179850 x y
           grind)
        | exact superpose b0e179850 b0e18
        | (have j1 := b0e179850 x y
           grind)
        | exact resolve b0e18 b0e179850
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e179850
      have b0e186705 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e186178
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e186178
        | (have j1 := b0e16 y x
           grind)
        | exact resolve b0e186178 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e186710 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e186178
           have i₂ := b0e7620 x y
           grind)
        | exact superpose b0e7620 b0e186178
        | (have j1 := b0e7620 x y
           grind)
        | (have r₁ := b0e186178
           have r₂ := b0e7620 x y
           grind)
        | exact resolve b0e186178 b0e7620
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7620 b0e186178
      have b0e186717 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e186710
      have b0e186718 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
      clear b0e186717
      have b0e186723 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e186705
      have b0e186724 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e186723
      have b0e186726 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have j1 := b0e14 y x
           grind)
        | (have r₁ := b0e186718
           have r₂ := b0e14 y x
           grind)
        | exact resolve b0e186718 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186718
      have b0e188929 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e13057 y x
           have i₂ := b0e186726
           grind)
        | exact superpose b0e186726 b0e13057
        | (have j0 := b0e13057 y x
           grind)
        | (have r₁ := b0e13057 y x
           have r₂ := b0e186726
           grind)
        | exact resolve b0e13057 b0e186726
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13057
      have b0e188946 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
      clear b0e186726
      have b0e188950 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
      clear b0e188929
      have b0e188961 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b0e188950
           have r₂ := b0e188946
           grind)
        | exact resolve b0e188950 b0e188946
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e188946 b0e188950
      have b0e236037 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e28 (σ X1) X0
           have i₂ := b0e128026 X1 (σ X0)
           grind)
        | exact superpose b0e128026 b0e28
        | (have j1 := b0e128026 X1 (σ X0)
           grind)
        | exact resolve b0e28 b0e128026
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28 b0e128026
      have b0e236042 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e236037 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e236037
        | (have j0 := b0e236037 X0 X1
           grind)
        | exact resolve b0e236037 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236037
      have b0e236055 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e236042 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e236042
        | (have j0 := b0e236042 X0 X1
           grind)
        | exact resolve b0e236042 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236042
      have b0e236062 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e236055 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e236055
        | (have j0 := b0e236055 X0 X1
           grind)
        | exact resolve b0e236055 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236055
      have b0e236066 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e236062 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e236062
        | (have j0 := b0e236062 X0 X1
           grind)
        | exact resolve b0e236062 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236062
      have b0e236067 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e236066 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e236066
        | (have j0 := b0e236066 X0 X1
           grind)
        | exact resolve b0e236066 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236066
      have b0e239328 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e236067 x y
           grind)
        | exact superpose b0e236067 b0e18
        | (have j1 := b0e236067 x y
           grind)
        | exact resolve b0e18 b0e236067
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e236067
      have b0e279878 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X0 (σ X1)
           have i₂ := b0e157475 X1 (σ X0)
           grind)
        | exact superpose b0e157475 b0e35
        | (have j1 := b0e157475 X1 (σ X0)
           grind)
        | exact resolve b0e35 b0e157475
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e157475
      have b0e279883 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e279878 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e279878
        | (have j0 := b0e279878 X0 X1
           grind)
        | exact resolve b0e279878 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279878
      have b0e279900 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e279883 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e279883
        | (have j0 := b0e279883 X0 X1
           grind)
        | exact resolve b0e279883 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279883
      have b0e279911 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e279900 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e279900
        | (have j0 := b0e279900 X0 X1
           grind)
        | exact resolve b0e279900 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279900
      have b0e279917 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e279911 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e279911
        | (have j0 := b0e279911 X0 X1
           grind)
        | exact resolve b0e279911 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279911
      have b0e279918 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e279917 X0 X1
           have i₂ := b0e51 X0
           grind)
        | exact superpose b0e51 b0e279917
        | (have j0 := b0e279917 X0 X1
           grind)
        | exact resolve b0e279917 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51 b0e279917
      have b0e286679 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e279918 y x
           grind)
        | exact superpose b0e279918 b0e18
        | (have j1 := b0e279918 y x
           grind)
        | exact resolve b0e18 b0e279918
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279918
      have b0e290613 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e286679
           have i₂ := b0e186724
           grind)
        | exact superpose b0e186724 b0e286679
        | exact resolve b0e286679 b0e186724
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e186724 b0e286679
      have b0e290614 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e290613
      have b0e290615 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e290614
      have b0e294443 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e188961
           have i₂ := b0e290615
           grind)
        | exact superpose b0e290615 b0e188961
        | exact resolve b0e188961 b0e290615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e188961 b0e290615
      have b0e294474 : (M.op x y) = (M.op x x) := by grind
      clear b0e294443
      have b0e298228 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e239328
           have i₂ := b0e294474
           grind)
        | exact superpose b0e294474 b0e239328
        | exact resolve b0e239328 b0e294474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e239328
      have b0e298230 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e294474
           grind)
        | exact superpose b0e294474 b0e15
        | (have j0 := b0e15 x x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e294474
           grind)
        | exact resolve b0e15 b0e294474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e298277 : (M.op y y) = (k y x) ∨ (M.op x x) = (M.op y y) := by grind
      clear b0e298230
      have b0e298278 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
      clear b0e298228
      have b0e298279 : (M.op x x) = (k y x) := by grind
      clear b0e298278
      have b0e302186 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e1425 x y
           have i₂ := b0e298279
           grind)
        | exact superpose b0e298279 b0e1425
        | (have j0 := b0e1425 x y
           grind)
        | exact resolve b0e1425 b0e298279
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1425
      have b0e302215 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e302186
      have b0e310653 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
        first
        | (have i₁ := b0e298279
           have i₂ := b0e298277
           grind)
        | exact superpose b0e298277 b0e298279
        | exact resolve b0e298279 b0e298277
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e298277 b0e298279
      have b0e310704 : (M.op x x) = (M.op y y) := by grind
      clear b0e310653
      have b0e336847 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e302215
           have i₂ := b0e310704
           grind)
        | exact superpose b0e310704 b0e302215
        | exact resolve b0e302215 b0e310704
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e302215 b0e310704
      have b0e336849 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
      clear b0e336847
      have b0e337063 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e336849
           grind)
        | exact superpose b0e336849 b0e18
        | exact resolve b0e18 b0e336849
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e336849
      have b0e337122 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e337063
           have i₂ := b0e294474
           grind)
        | exact superpose b0e294474 b0e337063
        | exact resolve b0e337063 b0e294474
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e294474 b0e337063
      have b0e337123 : False := by grind
      exact b0e337123
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : (M.op x x) = (M.op y x) := by grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e48 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e49 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b1e15 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e52 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b1e49
        have b1e53 : (k x y) = (M.op y y) := by grind
        clear b1e48
        have b1e54 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e52
          | exact resolve b1e52 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52
        have b1e55 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e51 y
             grind)
          | exact superpose b1e51 b1e54
          | exact resolve b1e54 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e51 (σ X0)
             grind)
          | exact superpose b1e51 b1e18
          | exact resolve b1e18 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e57 X0
             have i₂ := b1e51 X0
             grind)
          | exact superpose b1e51 b1e57
          | exact resolve b1e57 b1e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51 b1e57
        have b1e71 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e73 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e71 X0
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e71
          | (have j0 := b1e71 X0
             grind)
          | exact resolve b1e71 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e71
        have b1e122 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e21
          | exact resolve b1e21 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e126 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e122
             have i₂ := b1e64 x
             grind)
          | exact superpose b1e64 b1e122
          | exact resolve b1e122 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e614 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e73 (σ x)
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e73
          | (have j0 := b1e73 (σ x)
             grind)
          | (have r₁ := b1e73 (σ x)
             have r₂ := b1e55
             grind)
          | exact resolve b1e73 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e73
        have b1e619 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e614
        have b1e621 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e619
             have i₂ := b1e64 x
             grind)
          | exact superpose b1e64 b1e619
          | exact resolve b1e619 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e619
        have b1e623 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e621
             have r₂ := b1e126
             grind)
          | exact resolve b1e621 b1e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e621
        have b1e624 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e623
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e623
          | exact resolve b1e623 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e623
        have b1e625 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e624
             have i₂ := b1e53
             grind)
          | exact superpose b1e53 b1e624
          | exact resolve b1e624 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e624
        have b1e626 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e625
             have i₂ := b1e64 x
             grind)
          | exact superpose b1e64 b1e625
          | exact resolve b1e625 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e625
        have b1e627 : False := by grind
        exact b1e627
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e47 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49 : (k x y) = (M.op y y) := by grind
        clear b2e47
        have b2e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e48 (σ X0)
             grind)
          | exact superpose b2e48 b2e18
          | exact resolve b2e18 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e51 X0
             have i₂ := b2e48 X0
             grind)
          | exact superpose b2e48 b2e51
          | exact resolve b2e51 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48 b2e51
        have b2e86 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
        have b2e133 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e58 y
             grind)
          | exact superpose b2e58 b2e22
          | exact resolve b2e22 b2e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e58
        have b2e973 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e86 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e974 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e973
             have r₂ := b2e21
             grind)
          | exact resolve b2e973 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e973
        have b2e977 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e974
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e974
          | exact resolve b2e974 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e974
        have b2e979 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e977
             have i₂ := b2e49
             grind)
          | exact superpose b2e49 b2e977
          | exact resolve b2e977 b2e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49 b2e977
        have b2e980 : False := by grind
        exact b2e980
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : (M.op y x) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e51 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e52 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e49
        have b3e54 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e52
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e52
          | exact resolve b3e52 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e71 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e54
             grind)
          | exact superpose b3e54 b3e15
          | exact resolve b3e15 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e73
        have b3e78 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e77
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e77
          | exact resolve b3e77 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e77
        have b3e79 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e51 y
             grind)
          | exact superpose b3e51 b3e78
          | exact resolve b3e78 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51 b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op y x)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e79
          | exact resolve b3e79 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e128 : (k x y) = (τ (σ (M.op y x))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e80
             grind)
          | exact superpose b3e80 b3e13
          | exact resolve b3e13 b3e80
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e129 : (M.op y x) = (k x y) := by
          first
          | (have i₁ := b3e128
             have i₂ := b3e13 (M.op y x)
             grind)
          | exact superpose b3e13 b3e128
          | exact resolve b3e128 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e128
        have b3e243 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e71 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e244 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e243
             have r₂ := b3e20
             grind)
          | exact resolve b3e243 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e243
        have b3e247 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e129
             have i₂ := b3e244
             grind)
          | exact superpose b3e244 b3e129
          | exact resolve b3e129 b3e244
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e129 b3e244
        have b3e252 : False := by grind
        exact b3e252
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          have b4e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e25 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b4e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e25 X0 X1
               grind)
            | exact superpose b4e25 b4e14
            | exact resolve b4e14 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e26 X1 X0
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e30
            | exact resolve b4e30 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e63 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 : G, (M.op y x) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e16 y X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e16
            | (have j0 := b4e16 y X0
               grind)
            | exact resolve b4e16 b4e22
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
          have b4e67 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b4e63
          have b4e69 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
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
          have b4e71 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e69
               have i₂ := b4e66 y
               grind)
            | exact superpose b4e66 b4e69
            | exact resolve b4e69 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e72 : (M.op (σ y) (σ x)) = (σ (M.op y x)) := by
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
          have b4e74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e66 (σ X0)
               grind)
            | exact superpose b4e66 b4e19
            | exact resolve b4e19 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e77 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b4e26 X0 (τ X0)
               have i₂ := b4e66 (τ X0)
               grind)
            | exact superpose b4e66 b4e26
            | exact resolve b4e26 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26
          have b4e80 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e77 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e77
            | exact resolve b4e77 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e74 X0
               have i₂ := b4e66 X0
               grind)
            | exact superpose b4e66 b4e74
            | exact resolve b4e74 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e86 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b4e80 X0
               have i₂ := b4e66 X0
               grind)
            | exact superpose b4e66 b4e80
            | exact resolve b4e80 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66 b4e80
          have b4e96 : (M.op (σ x) (σ x)) ≠ (σ (M.op y x)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e72
               grind)
            | exact superpose b4e72 b4e23
            | exact resolve b4e23 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e100 : (σ (M.op y x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e96
               have i₂ := b4e83 x
               grind)
            | exact superpose b4e83 b4e96
            | exact resolve b4e96 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96
          have b4e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X0 X0
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e116 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e124 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b4e130 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e116 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e116
          have b4e134 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e137 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e124 X0 X1
               have i₂ := b4e83 X1
               grind)
            | exact superpose b4e83 b4e124
            | (have j0 := b4e124 X0 X1
               grind)
            | exact resolve b4e124 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e124
          have b4e140 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e132 X0 X1
               have j1 := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X0 X1
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X1 X0
               have r₂ := b4e130 X0 X1
               grind)
            | (have r₁ := b4e132 X1 X1
               have r₂ := b4e130 X1 X1
               grind)
            | exact resolve b4e132 b4e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132
          have b4e146 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e137 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e137
            | (have j0 := b4e137 X0 X1
               grind)
            | exact resolve b4e137 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137
          have b4e164 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e16
            | (have j0 := b4e16 (σ X0) X1
               grind)
            | exact resolve b4e16 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e177 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e86 X0
               have i₂ := b4e18 X1 (τ X0)
               grind)
            | (have i₁ := b4e86 X0
               have i₂ := b4e18 (τ X0) (τ X0)
               grind)
            | exact superpose b4e18 b4e86
            | (have j1 := b4e18 X1 (τ X0)
               grind)
            | exact resolve b4e86 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e184 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op (τ X0) (τ X0))
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e14
            | exact resolve b4e14 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e254 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (τ X0) X1
               have i₂ := b4e184 X0
               grind)
            | exact superpose b4e184 b4e16
            | (have j0 := b4e16 (τ X0) X1
               grind)
            | exact resolve b4e16 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e391 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op y x) ∨ (M.op y x) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e130 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e130
            | (have j0 := b4e130 X0 y
               grind)
            | exact resolve b4e130 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e490 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X1 X0
               have i₂ := b4e134 (τ X1) X0
               grind)
            | exact superpose b4e134 b4e25
            | (have j1 := b4e134 (τ X1) X0
               grind)
            | exact resolve b4e25 b4e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e636 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e140 (σ X1) (σ X0)
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e140
            | (have j0 := b4e140 (σ X1) (σ X0)
               grind)
            | exact resolve b4e140 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e673 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e25 X0 X1
               have i₂ := b4e140 X1 (τ X0)
               grind)
            | exact superpose b4e140 b4e25
            | (have j1 := b4e140 X1 (τ X0)
               grind)
            | exact resolve b4e25 b4e140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e140
          have b4e715 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e673 X0 X1
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e673
            | (have j0 := b4e673 X0 X1
               grind)
            | exact resolve b4e673 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e673
          have b4e731 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e636 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e636
            | (have j0 := b4e636 X0 X1
               grind)
            | exact resolve b4e636 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e636
          have b4e748 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e715 X0 X1
               have i₂ := b4e184 X0
               grind)
            | exact superpose b4e184 b4e715
            | (have j0 := b4e715 X0 X1
               grind)
            | exact resolve b4e715 b4e184
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e184 b4e715
          have b4e761 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e731 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e731
            | (have j0 := b4e731 X0 X1
               grind)
            | exact resolve b4e731 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e731
          have b4e2066 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e146 X1 X0
               grind)
            | exact superpose b4e146 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e146 X1 X0
               grind)
            | exact resolve b4e16 b4e146
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2082 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e2085 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e146 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e146
          have b4e2143 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e2066 X0 X1
               have j1 := b4e164 X0 (σ X1)
               grind)
            | (have r₁ := b4e2066 X0 X0
               have r₂ := b4e164 X0 (σ X0)
               grind)
            | (have r₁ := b4e2066 X0 X1
               have r₂ := b4e164 X0 (σ X1)
               grind)
            | exact resolve b4e2066 b4e164
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e164 b4e2066
          have b4e2227 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2143 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e2143
            | (have j0 := b4e2143 X0 X1
               grind)
            | exact resolve b4e2143 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2143
          have b4e2279 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2227 X0 X1
               have i₂ := b4e83 X1
               grind)
            | exact superpose b4e83 b4e2227
            | (have j0 := b4e2227 X0 X1
               grind)
            | exact resolve b4e2227 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2227
          have b4e2308 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e2279 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e2279
            | (have j0 := b4e2279 X0 X1
               grind)
            | exact resolve b4e2279 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2279
          have b4e10077 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e490 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e490
            | exact resolve b4e490 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e490
          have b4e10368 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e10077 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e10077
            | (have j0 := b4e10077 X0 X1
               grind)
            | exact resolve b4e10077 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10077
          have b4e12028 : ∀ X0 : G, (τ (M.op (σ y) (σ x))) = (M.op X0 (τ (σ y))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e748 (σ y) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e748
            | (have j0 := b4e748 (σ y) X0
               grind)
            | exact resolve b4e748 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e12211 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e254 X0 X1
               have i₂ := b4e748 X0 X1
               grind)
            | exact superpose b4e748 b4e254
            | (have j0 := b4e254 X0 X1
               have j1 := b4e748 X0 X1
               grind)
            | (have r₁ := b4e254 X0 X1
               have r₂ := b4e748 X0 X1
               grind)
            | exact resolve b4e254 b4e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e254 b4e748
          have b4e12440 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e12211 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12211
          have b4e12598 : ∀ X0 : G, (M.op X0 y) = (τ (M.op (σ y) (σ x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12028 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e12028
            | (have j0 := b4e12028 X0
               grind)
            | exact resolve b4e12028 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12028
          have b4e12699 : ∀ X0 : G, (M.op X0 y) = (τ (σ (M.op y x))) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12598 X0
               have i₂ := b4e72
               grind)
            | exact superpose b4e72 b4e12598
            | (have j0 := b4e12598 X0
               grind)
            | exact resolve b4e12598 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12598
          have b4e12761 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ X0)) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12699 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e12699
            | (have j0 := b4e12699 X0
               grind)
            | exact resolve b4e12699 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12699
          have b4e12800 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12761 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e12761
            | (have j0 := b4e12761 X0
               grind)
            | exact resolve b4e12761 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12761
          have b4e12818 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op y x) = (M.op X0 y) ∨ (k (τ (σ y)) X0) = (M.op X0 (τ (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e12800 X0
               have i₂ := b4e72
               grind)
            | exact superpose b4e72 b4e12800
            | (have j0 := b4e12800 X0
               grind)
            | exact resolve b4e12800 b4e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72 b4e12800
          have b4e12828 : ∀ X0 : G, (σ (M.op y x)) = (σ (k y X0)) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e12818 X0
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e12818
            | (have j0 := b4e12818 X0
               grind)
            | exact resolve b4e12818 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12818
          have b4e21829 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (σ X0) (σ X1)
               have i₂ := b4e761 X0 X1
               grind)
            | exact superpose b4e761 b4e17
            | (have j0 := b4e17 (σ X0) (σ X1)
               have j1 := b4e761 X0 X1
               grind)
            | exact resolve b4e17 b4e761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e761
          have b4e21992 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21829 X0 X1
               have i₂ := b4e83 X1
               grind)
            | exact superpose b4e83 b4e21829
            | (have j0 := b4e21829 X0 X1
               grind)
            | exact resolve b4e21829 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21829
          have b4e22156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21992 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e21992
            | (have j0 := b4e21992 X0 X1
               grind)
            | exact resolve b4e21992 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21992
          have b4e22157 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e22156 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22156
          have b4e22262 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e22157 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e22157
            | (have j0 := b4e22157 X0 X1
               grind)
            | exact resolve b4e22157 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22157
          have b4e22305 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e22262 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e22262
            | (have j0 := b4e22262 X0 X1
               grind)
            | exact resolve b4e22262 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22262
          have b4e22306 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e22305 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22305
          have b4e22372 : ∀ X0 : G, (k y X0) = (τ (σ (M.op y x))) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e14 (k y X0)
               have i₂ := b4e12828 X0
               grind)
            | exact superpose b4e12828 b4e14
            | (have j1 := b4e12828 X0
               grind)
            | exact resolve b4e14 b4e12828
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12828
          have b4e22440 : ∀ X0 : G, (M.op y x) = (k y X0) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e22372 X0
               have i₂ := b4e14 (M.op y x)
               grind)
            | exact superpose b4e14 b4e22372
            | (have j0 := b4e22372 X0
               grind)
            | exact resolve b4e22372 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22372
          have b4e22815 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e134 y X0
               have i₂ := b4e22440 X0
               grind)
            | exact superpose b4e22440 b4e134
            | (have j0 := b4e134 y X0
               have j1 := b4e22440 X0
               grind)
            | exact resolve b4e134 b4e22440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134 b4e22440
          have b4e22869 : ∀ X0 : G, (M.op y x) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op y x) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 y) = (k y X0) := by
            intro X0
            first
            | (have j0 := b4e22815 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22815
          have b4e22891 : ∀ X0 : G, (M.op X0 y) = (k y X0) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e22869 X0
               have j1 := b4e391 X0
               grind)
            | (have r₁ := b4e22869 y
               have r₂ := b4e391 y
               grind)
            | (have r₁ := b4e22869 X0
               have r₂ := b4e391 X0
               grind)
            | exact resolve b4e22869 b4e391
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e391 b4e22869
          have b4e23233 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e22891 X0
               have i₂ := b4e10368 y X0
               grind)
            | exact superpose b4e10368 b4e22891
            | (have j0 := b4e22891 X0
               have j1 := b4e10368 y X0
               grind)
            | exact resolve b4e22891 b4e10368
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10368
          have b4e23417 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e23233 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23233
          have b4e25199 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2082 (τ X0) (τ X1)
               have i₂ := b4e41 X0 X1
               grind)
            | exact superpose b4e41 b4e2082
            | (have j0 := b4e2082 (τ X1) (τ X0)
               grind)
            | exact resolve b4e2082 b4e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41 b4e2082
          have b4e25349 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25199 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e25199
            | (have j0 := b4e25199 X0 X1
               grind)
            | exact resolve b4e25199 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25199
          have b4e25402 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25349 X0 X1
               have i₂ := b4e86 X1
               grind)
            | exact superpose b4e86 b4e25349
            | (have j0 := b4e25349 X0 X1
               grind)
            | exact resolve b4e25349 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25349
          have b4e25444 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25402 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e25402
            | (have j0 := b4e25402 X0 X1
               grind)
            | exact resolve b4e25402 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25402
          have b4e25471 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25444 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e25444
            | (have j0 := b4e25444 X0 X1
               grind)
            | exact resolve b4e25444 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25444
          have b4e25496 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e25471 X0 X1
               have i₂ := b4e86 X0
               grind)
            | exact superpose b4e86 b4e25471
            | (have j0 := b4e25471 X0 X1
               grind)
            | exact resolve b4e25471 b4e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e86 b4e25471
          have b4e25518 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e25496 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e25496
            | (have j0 := b4e25496 X0 X1
               grind)
            | exact resolve b4e25496 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25496
          have b4e25527 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e25518 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e25518
            | (have j0 := b4e25518 X0 X1
               grind)
            | exact resolve b4e25518 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25518
          have b4e25536 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e25527 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e25527
            | (have j0 := b4e25527 X0 X1
               grind)
            | exact resolve b4e25527 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25527
          have b4e92439 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 (σ X1)
               have i₂ := b4e12440 (σ X0) X1
               grind)
            | exact superpose b4e12440 b4e38
            | (have j1 := b4e12440 (σ X0) X1
               grind)
            | exact resolve b4e38 b4e12440
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12440
          have b4e92856 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e92439 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e92439
            | (have j0 := b4e92439 X0 X1
               grind)
            | exact resolve b4e92439 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92439
          have b4e93370 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e92856 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e92856
            | (have j0 := b4e92856 X0 X1
               grind)
            | exact resolve b4e92856 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92856
          have b4e93681 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93370 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e93370
            | (have j0 := b4e93370 X0 X1
               grind)
            | exact resolve b4e93370 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93370
          have b4e93891 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e93681 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e93681
            | (have j0 := b4e93681 X0 X1
               grind)
            | exact resolve b4e93681 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93681
          have b4e94004 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e93891 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e93891
            | (have j0 := b4e93891 X0 X1
               grind)
            | exact resolve b4e93891 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93891
          have b4e96472 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e38 X0 X1
               have i₂ := b4e94004 (σ X0) X1
               grind)
            | exact superpose b4e94004 b4e38
            | (have j1 := b4e94004 (σ X0) X1
               grind)
            | exact resolve b4e38 b4e94004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e96599 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e94004 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e94004
          have b4e96858 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e96472 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e96472
            | (have j0 := b4e96472 X0 X1
               grind)
            | exact resolve b4e96472 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96472
          have b4e97614 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e96858 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e96858
            | (have j0 := b4e96858 X0 X1
               grind)
            | exact resolve b4e96858 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e96858
          have b4e99117 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e96599 y X0
               have i₂ := b4e23417 X0
               grind)
            | (have i₁ := b4e96599 X0 X0
               have i₂ := b4e23417 X0
               grind)
            | exact superpose b4e23417 b4e96599
            | (have j0 := b4e96599 y X0
               have j1 := b4e23417 X0
               grind)
            | (have r₁ := b4e96599 y y
               have r₂ := b4e23417 y
               grind)
            | (have r₁ := b4e96599 y X0
               have r₂ := b4e23417 X0
               grind)
            | (have r₁ := b4e96599 x y
               have r₂ := b4e23417 y
               grind)
            | exact resolve b4e96599 b4e23417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23417 b4e96599
          have b4e99245 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op y x) = (M.op X0 y) := by
            intro X0
            first
            | (have j0 := b4e99117 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99117
          have b4e99417 : ∀ X0 : G, (M.op X0 X0) = (k y X0) ∨ (M.op y y) = (k y X0) ∨ (σ (k y X0)) = (σ (M.op X0 y)) := by
            intro X0
            first
            | (have j0 := b4e99245 X0
               have j1 := b4e64 X0
               grind)
            | (have r₁ := b4e99245 X0
               have r₂ := b4e64 X0
               grind)
            | exact resolve b4e99245 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99245
          have b4e99524 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op y x) = (k y X0) := by
            intro X0
            first
            | (have i₁ := b4e99417 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e99417
            | (have j0 := b4e99417 X0
               grind)
            | exact resolve b4e99417 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99417
          have b4e270837 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e30 (σ X1) X0
               have i₂ := b4e97614 X1 (σ X0)
               grind)
            | exact superpose b4e97614 b4e30
            | (have j1 := b4e97614 X1 (σ X0)
               grind)
            | exact resolve b4e30 b4e97614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e97614
          have b4e270848 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e270837 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e270837
            | (have j0 := b4e270837 X0 X1
               grind)
            | exact resolve b4e270837 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270837
          have b4e270888 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e270848 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e270848
            | (have j0 := b4e270848 X0 X1
               grind)
            | exact resolve b4e270848 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270848
          have b4e270918 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e270888 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e270888
            | (have j0 := b4e270888 X0 X1
               grind)
            | exact resolve b4e270888 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270888
          have b4e270939 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e270918 X0 X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e270918
            | (have j0 := b4e270918 X0 X1
               grind)
            | exact resolve b4e270918 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270918
          have b4e270951 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e270939 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e270939
            | (have j0 := b4e270939 X0 X1
               grind)
            | exact resolve b4e270939 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270939
          have b4e290230 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e270951 x y
               grind)
            | exact superpose b4e270951 b4e20
            | (have j1 := b4e270951 x y
               grind)
            | exact resolve b4e20 b4e270951
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e270951
          have b4e290353 : (M.op y x) = (k y x) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e290230
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e290230
            | exact resolve b4e290230 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e290230
          have b4e290390 : (M.op y x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e99524 x
               grind)
            | (have r₁ := b4e290353
               have r₂ := b4e99524 x
               grind)
            | exact resolve b4e290353 b4e99524
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e99524 b4e290353
          have b4e292942 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e290390
               have i₂ := b4e22891 x
               grind)
            | exact superpose b4e22891 b4e290390
            | (have j1 := b4e22891 x
               grind)
            | exact resolve b4e290390 b4e22891
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22891
          have b4e292965 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e2308 y x
               have i₂ := b4e290390
               grind)
            | exact superpose b4e290390 b4e2308
            | (have j0 := b4e2308 y x
               grind)
            | exact resolve b4e2308 b4e290390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2308
          have b4e293002 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e292942
          have b4e293016 : (σ (M.op y y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have r₁ := b4e292965
               have r₂ := b4e100
               grind)
            | exact resolve b4e292965 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e292965
          have b4e293045 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e293016
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e293016
            | exact resolve b4e293016 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293016
          have b4e293046 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b4e293045
          have b4e306015 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e293046
               grind)
            | exact superpose b4e293046 b4e20
            | exact resolve b4e20 b4e293046
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293046
          have b4e1546158 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e177 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e177
            | exact resolve b4e177 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e177
          have b4e1546178 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e1546158 X0 X1
               have i₂ := b4e83 X0
               grind)
            | exact superpose b4e83 b4e1546158
            | (have j0 := b4e1546158 X0 X1
               grind)
            | exact resolve b4e1546158 b4e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e83 b4e1546158
          have b4e1547878 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have i₁ := b4e306015
               have i₂ := b4e1546178 x y
               grind)
            | exact superpose b4e1546178 b4e306015
            | (have j1 := b4e1546178 x y
               grind)
            | (have r₁ := b4e306015
               have r₂ := b4e1546178 x y
               grind)
            | exact resolve b4e306015 b4e1546178
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e306015 b4e1546178
          have b4e1547911 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
          clear b4e1547878
          have b4e1547932 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
            first
            | (have j1 := b4e25536 y x
               grind)
            | (have r₁ := b4e1547911
               have r₂ := b4e25536 y x
               grind)
            | exact resolve b4e1547911 b4e25536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25536 b4e1547911
          have b4e1547953 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e1547932
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1547932
            | exact resolve b4e1547932 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1547932
          have b4e1552839 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e1547953
               have i₂ := b4e290390
               grind)
            | exact superpose b4e290390 b4e1547953
            | exact resolve b4e1547953 b4e290390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e290390 b4e1547953
          have b4e1552962 : (M.op x y) = (M.op y x) ∨ (M.op x x) = (k y x) := by grind
          clear b4e1552839
          have b4e1552967 : (M.op x x) = (k y x) := by
            first
            | (have j1 := b4e64 x
               grind)
            | (have r₁ := b4e1552962
               have r₂ := b4e64 x
               grind)
            | exact resolve b4e1552962 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64 b4e1552962
          have b4e1557710 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e2085 x y
               have i₂ := b4e1552967
               grind)
            | exact superpose b4e1552967 b4e2085
            | (have j0 := b4e2085 x y
               grind)
            | exact resolve b4e2085 b4e1552967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e2085
          have b4e1557734 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b4e1557710
          have b4e1557759 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e1557734
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e1557734
            | exact resolve b4e1557734 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1557734
          have b4e1579720 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1557759
               grind)
            | exact superpose b4e1557759 b4e20
            | exact resolve b4e20 b4e1557759
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1557759
          have b4e1579739 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e1579720
               have i₂ := b4e293002
               grind)
            | exact superpose b4e293002 b4e1579720
            | exact resolve b4e1579720 b4e293002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e293002 b4e1579720
          have b4e1579746 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b4e1579739
          have b4e3344601 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e22306 y x
               have i₂ := b4e1552967
               grind)
            | exact superpose b4e1552967 b4e22306
            | (have j0 := b4e22306 y x
               grind)
            | exact resolve b4e22306 b4e1552967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22306
          have b4e3344603 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b4e3344601
          have b4e3344605 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e3344603
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e3344603
            | exact resolve b4e3344603 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344603
          have b4e3344607 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e3344605
               have r₂ := b4e100
               grind)
            | exact resolve b4e3344605 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344605
          have b4e3344609 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
            first
            | (have i₁ := b4e3344607
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e3344607
            | exact resolve b4e3344607 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344607
          have b4e3344623 : (σ (M.op y x)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b4e1579746
               have i₂ := b4e3344609
               grind)
            | exact superpose b4e3344609 b4e1579746
            | exact resolve b4e1579746 b4e3344609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1579746 b4e3344609
          have b4e3344683 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b4e3344623
               have r₂ := b4e100
               grind)
            | exact resolve b4e3344623 b4e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e100 b4e3344623
          have b4e3344764 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e3344683
               grind)
            | exact superpose b4e3344683 b4e17
            | (have j0 := b4e17 x x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e3344683
               grind)
            | exact resolve b4e17 b4e3344683
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344683
          have b4e3344789 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
          clear b4e3344764
          have b4e3344796 : (M.op x x) = (M.op y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b4e3344789
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e3344789
            | exact resolve b4e3344789 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344789
          have b4e3344802 : (M.op y y) = (k y x) := by
            first
            | (have r₁ := b4e3344796
               have r₂ := b4e21
               grind)
            | exact resolve b4e3344796 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344796
          have b4e3344803 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b4e3344802
               have i₂ := b4e1552967
               grind)
            | exact superpose b4e1552967 b4e3344802
            | exact resolve b4e3344802 b4e1552967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1552967 b4e3344802
          have b4e3344814 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b4e22
               have i₂ := b4e3344803
               grind)
            | exact superpose b4e3344803 b4e22
            | exact resolve b4e22 b4e3344803
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3344803
          have b4e3345160 : False := by grind
          exact b4e3345160
        · have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
          have b5e85 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (M.op X0 X0) = (M.op y X0) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e120 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op (σ y) X0) = (k X0 (σ y)) := by
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
          have b5e228 : (M.op x x) = (M.op y x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e229 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e228
               have r₂ := b5e21
               grind)
            | exact resolve b5e228 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e228
          have b5e1179 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1180 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1179
               have r₂ := b5e23
               grind)
            | exact resolve b5e1179 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1179
          have b5e1184 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1180
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1180
            | exact resolve b5e1180 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1180
          have b5e1188 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1184
               have i₂ := b5e229
               grind)
            | exact superpose b5e229 b5e1184
            | exact resolve b5e1184 b5e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e229 b5e1184
          have b5e1195 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1188
               grind)
            | exact superpose b5e1188 b5e23
            | exact resolve b5e23 b5e1188
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1188
          have b5e1205 : False := by grind
          exact b5e1205
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e47 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e49 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e47
        have b6e50 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e49
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e49
          | exact resolve b6e49 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e67 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e50
             grind)
          | exact superpose b6e50 b6e15
          | exact resolve b6e15 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e71 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e67
        have b6e72 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e71
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e71
          | exact resolve b6e71 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e73 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e48 y
             grind)
          | exact superpose b6e48 b6e72
          | exact resolve b6e72 b6e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e48 b6e72
        have b6e122 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e73
             grind)
          | exact superpose b6e73 b6e13
          | exact resolve b6e13 b6e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e73
        have b6e123 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e122
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e122
          | exact resolve b6e122 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e122
        have b6e140 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e123
             grind)
          | exact superpose b6e123 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e123
        have b6e141 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e140
        have b6e143 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e141
             have r₂ := b6e21
             grind)
          | exact resolve b6e141 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e141
        have b6e145 : False := by grind
        exact b6e145
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e61 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by
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
          have b7e64 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) := by grind
          clear b7e61
          have b7e65 : (M.op (σ y) (σ x)) = (σ (k y y)) := by
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
          have b7e66 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
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
          have b7e86 : ∀ X0 : G, (M.op (σ y) (σ x)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op (σ y) X0) ∨ (M.op X0 X0) = (M.op (σ y) X0) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e93 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
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
          have b7e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b7e127 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e102
          have b7e665 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e670 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e665
          have b7e672 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e670
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e670
            | exact resolve b7e670 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e670
          have b7e674 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e672
               have r₂ := b7e93
               grind)
            | exact resolve b7e672 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e672
          have b7e675 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e674
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e674
            | exact resolve b7e674 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e674
          have b7e676 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e675
               have i₂ := b7e77 x
               grind)
            | exact superpose b7e77 b7e675
            | exact resolve b7e675 b7e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77 b7e675
          have b7e678 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have i₁ := b7e676
               have i₂ := b7e127 x y
               grind)
            | exact superpose b7e127 b7e676
            | (have j1 := b7e127 x y
               grind)
            | exact resolve b7e676 b7e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e127
          have b7e680 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e676
               grind)
            | exact superpose b7e676 b7e14
            | exact resolve b7e14 b7e676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e676
          have b7e703 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e680
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e680
            | exact resolve b7e680 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e680
          have b7e705 : (M.op y x) = (k x y) ∨ (M.op y x) = (M.op y y) := by
            first
            | (have r₁ := b7e678
               have r₂ := b7e93
               grind)
            | exact resolve b7e678 b7e93
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93 b7e678
          have b7e708 : (M.op y x) = (k x y) := by
            first
            | (have r₁ := b7e705
               have r₂ := b7e22
               grind)
            | exact resolve b7e705 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e705
          have b7e709 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e708
               have i₂ := b7e703
               grind)
            | exact superpose b7e703 b7e708
            | exact resolve b7e708 b7e703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e703 b7e708
          have b7e710 : False := by grind
          exact b7e710
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e26 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b8e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e14 (k X0 (τ X1))
               have i₂ := b8e26 X1 X0
               grind)
            | exact superpose b8e26 b8e14
            | exact resolve b8e14 b8e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 (τ X0)
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e30
            | exact resolve b8e30 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e62 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e60 (σ X0)
               grind)
            | exact superpose b8e60 b8e19
            | exact resolve b8e19 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e65 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e60 (τ X0)
               grind)
            | exact superpose b8e60 b8e26
            | exact resolve b8e26 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e65 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e65
            | exact resolve b8e65 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65
          have b8e71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e62 X0
               have i₂ := b8e60 X0
               grind)
            | exact superpose b8e60 b8e62
            | exact resolve b8e62 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e74 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e68 X0
               have i₂ := b8e60 X0
               grind)
            | exact superpose b8e60 b8e68
            | exact resolve b8e68 b8e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60 b8e68
          have b8e88 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e16
            | (have j0 := b8e16 (σ X0) X1
               grind)
            | exact resolve b8e16 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e115 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
          have b8e121 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e123 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e106 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e128 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e115 X0 X1
               have i₂ := b8e71 X1
               grind)
            | exact superpose b8e71 b8e115
            | (have j0 := b8e115 X0 X1
               grind)
            | exact resolve b8e115 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e115
          have b8e130 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e123 X0 X1
               have j1 := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X0 X1
               have r₂ := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X0
               have r₂ := b8e121 X0 X1
               grind)
            | (have r₁ := b8e123 X1 X1
               have r₂ := b8e121 X1 X1
               grind)
            | exact resolve b8e123 b8e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e121 b8e123
          have b8e133 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e128 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e128
            | (have j0 := b8e128 X0 X1
               grind)
            | exact resolve b8e128 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e145 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e14 (M.op (τ X0) (τ X0))
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e14
            | exact resolve b8e14 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e211 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (M.op X1 (τ X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (τ X0) X1
               have i₂ := b8e145 X0
               grind)
            | exact superpose b8e145 b8e16
            | (have j0 := b8e16 (τ X0) X1
               grind)
            | exact resolve b8e16 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e375 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) (τ X0))) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X0 X1
               have i₂ := b8e130 X1 (τ X0)
               grind)
            | exact superpose b8e130 b8e25
            | (have j1 := b8e130 X1 (τ X0)
               grind)
            | exact resolve b8e25 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e390 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (k X1 (τ X0)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e130 (τ X0) X1
               grind)
            | exact superpose b8e130 b8e26
            | (have j1 := b8e130 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e130
          have b8e406 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e375 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e375
            | (have j0 := b8e375 X0 X1
               grind)
            | exact resolve b8e375 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e375
          have b8e429 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ X0)) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e406 X0 X1
               have i₂ := b8e145 X0
               grind)
            | exact superpose b8e145 b8e406
            | (have j0 := b8e406 X0 X1
               grind)
            | exact resolve b8e406 b8e145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145 b8e406
          have b8e1361 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 (σ X0) (σ X1)
               have i₂ := b8e133 X1 X0
               grind)
            | exact superpose b8e133 b8e16
            | (have j0 := b8e16 (σ X0) (σ X1)
               have j1 := b8e133 X1 X0
               grind)
            | exact resolve b8e16 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1377 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1379 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1380 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1381 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e1425 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e1361 X0 X1
               have j1 := b8e88 X0 (σ X1)
               grind)
            | (have r₁ := b8e1361 X0 X0
               have r₂ := b8e88 X0 (σ X0)
               grind)
            | (have r₁ := b8e1361 X0 X1
               have r₂ := b8e88 X0 (σ X1)
               grind)
            | exact resolve b8e1361 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88 b8e1361
          have b8e1479 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1425 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e1425
            | (have j0 := b8e1425 X0 X1
               grind)
            | exact resolve b8e1425 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1425
          have b8e1515 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1479 X0 X1
               have i₂ := b8e71 X1
               grind)
            | exact superpose b8e71 b8e1479
            | (have j0 := b8e1479 X0 X1
               grind)
            | exact resolve b8e1479 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1479
          have b8e1537 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1515 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e1515
            | (have j0 := b8e1515 X0 X1
               grind)
            | exact resolve b8e1515 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1515
          have b8e5307 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e390 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e390
            | exact resolve b8e390 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e390
          have b8e5507 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e5307 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e5307
            | (have j0 := b8e5307 X0 X1
               grind)
            | exact resolve b8e5307 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5307
          have b8e5823 : ∀ X0 X1 : G, (τ (M.op X0 X0)) ≠ (τ (M.op X0 X0)) ∨ (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e211 X0 X1
               have i₂ := b8e429 X0 X1
               grind)
            | exact superpose b8e429 b8e211
            | (have j0 := b8e211 X0 X1
               have j1 := b8e429 X0 X1
               grind)
            | (have r₁ := b8e211 X0 X1
               have r₂ := b8e429 X0 X1
               grind)
            | exact resolve b8e211 b8e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e211 b8e429
          have b8e5976 : ∀ X0 X1 : G, (M.op X1 X1) = (k (τ X0) X1) ∨ (M.op X0 X0) = (k X0 (σ X1)) ∨ (k (τ X0) X1) = (M.op X1 (τ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e5823 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5823
          have b8e10415 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1537 (τ X1) (τ X0)
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e1537
            | (have j0 := b8e1537 (τ X0) (τ X1)
               grind)
            | exact resolve b8e1537 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1537
          have b8e10497 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10415 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e10415
            | (have j0 := b8e10415 X0 X1
               grind)
            | exact resolve b8e10415 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10415
          have b8e10527 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10497 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e10497
            | (have j0 := b8e10497 X0 X1
               grind)
            | exact resolve b8e10497 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10497
          have b8e10548 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10527 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e10527
            | (have j0 := b8e10527 X0 X1
               grind)
            | exact resolve b8e10527 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10527
          have b8e10563 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e10548 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e10548
            | (have j0 := b8e10548 X0 X1
               grind)
            | exact resolve b8e10548 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10548
          have b8e10572 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10563 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e10563
            | (have j0 := b8e10563 X0 X1
               grind)
            | exact resolve b8e10563 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10563
          have b8e10577 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10572 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e10572
            | (have j0 := b8e10572 X0 X1
               grind)
            | exact resolve b8e10572 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10572
          have b8e10578 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10577 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e10577
            | (have j0 := b8e10577 X0 X1
               grind)
            | exact resolve b8e10577 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10577
          have b8e15997 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1377 (τ X0) (τ X1)
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e1377
            | (have j0 := b8e1377 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1377 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1377
          have b8e16105 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e15997 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e15997
            | (have j0 := b8e15997 X0 X1
               grind)
            | exact resolve b8e15997 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e15997
          have b8e16146 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e16105 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e16105
            | (have j0 := b8e16105 X0 X1
               grind)
            | exact resolve b8e16105 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16105
          have b8e16178 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e16146 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e16146
            | (have j0 := b8e16146 X0 X1
               grind)
            | exact resolve b8e16146 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16146
          have b8e16203 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e16178 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e16178
            | (have j0 := b8e16178 X0 X1
               grind)
            | exact resolve b8e16178 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16178
          have b8e16226 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e16203 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e16203
            | (have j0 := b8e16203 X0 X1
               grind)
            | exact resolve b8e16203 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16203
          have b8e16246 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16226 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e16226
            | (have j0 := b8e16226 X0 X1
               grind)
            | exact resolve b8e16226 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16226
          have b8e16253 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16246 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e16246
            | (have j0 := b8e16246 X0 X1
               grind)
            | exact resolve b8e16246 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16246
          have b8e16260 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16253 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e16253
            | (have j0 := b8e16253 X0 X1
               grind)
            | exact resolve b8e16253 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16253
          have b8e17624 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1380 (τ X1) (τ X0)
               have i₂ := b8e40 X1 X0
               grind)
            | exact superpose b8e40 b8e1380
            | (have j0 := b8e1380 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1380 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1380
          have b8e17733 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X1) (τ X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17624 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e17624
            | (have j0 := b8e17624 X0 X1
               grind)
            | exact resolve b8e17624 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17624
          have b8e17780 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17733 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e17733
            | (have j0 := b8e17733 X0 X1
               grind)
            | exact resolve b8e17733 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17733
          have b8e17816 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17780 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e17780
            | (have j0 := b8e17780 X0 X1
               grind)
            | exact resolve b8e17780 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17780
          have b8e17845 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17816 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e17816
            | (have j0 := b8e17816 X0 X1
               grind)
            | exact resolve b8e17816 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17816
          have b8e17870 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e17845 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e17845
            | (have j0 := b8e17845 X0 X1
               grind)
            | exact resolve b8e17845 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17845
          have b8e17893 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17870 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e17870
            | (have j0 := b8e17870 X0 X1
               grind)
            | exact resolve b8e17870 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17870
          have b8e17910 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17893 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e17893
            | (have j0 := b8e17893 X0 X1
               grind)
            | exact resolve b8e17893 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17893
          have b8e17923 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17910 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e17910
            | (have j0 := b8e17910 X0 X1
               grind)
            | exact resolve b8e17910 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17910
          have b8e18171 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e1381 (τ X1) (τ X0)
               have i₂ := b8e40 X1 X0
               grind)
            | exact superpose b8e40 b8e1381
            | (have j0 := b8e1381 (τ X1) (τ X0)
               grind)
            | exact resolve b8e1381 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1381
          have b8e18281 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18171 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e18171
            | (have j0 := b8e18171 X0 X1
               grind)
            | exact resolve b8e18171 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18171
          have b8e18325 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18281 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e18281
            | (have j0 := b8e18281 X0 X1
               grind)
            | exact resolve b8e18281 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18281
          have b8e18361 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18325 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e18325
            | (have j0 := b8e18325 X0 X1
               grind)
            | exact resolve b8e18325 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18325
          have b8e18390 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18361 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e18361
            | (have j0 := b8e18361 X0 X1
               grind)
            | exact resolve b8e18361 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18361
          have b8e18415 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e18390 X0 X1
               have i₂ := b8e74 X1
               grind)
            | exact superpose b8e74 b8e18390
            | (have j0 := b8e18390 X0 X1
               grind)
            | exact resolve b8e18390 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18390
          have b8e18436 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e18415 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e18415
            | (have j0 := b8e18415 X0 X1
               grind)
            | exact resolve b8e18415 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18415
          have b8e18453 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e18436 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e18436
            | (have j0 := b8e18436 X0 X1
               grind)
            | exact resolve b8e18436 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18436
          have b8e18466 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X0 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e18453 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e18453
            | (have j0 := b8e18453 X0 X1
               grind)
            | exact resolve b8e18453 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18453
          have b8e80901 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X1)) X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 (τ X1)
               have i₂ := b8e5976 X1 (τ X0)
               grind)
            | exact superpose b8e5976 b8e26
            | (have j1 := b8e5976 X1 (τ X0)
               grind)
            | exact resolve b8e26 b8e5976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26
          have b8e81268 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 (σ X1)
               have i₂ := b8e5976 (σ X0) X1
               grind)
            | exact superpose b8e5976 b8e37
            | (have j1 := b8e5976 (σ X0) X1
               grind)
            | exact resolve b8e37 b8e5976
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5976
          have b8e81685 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e81268 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e81268
            | (have j0 := b8e81268 X0 X1
               grind)
            | exact resolve b8e81268 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81268
          have b8e81833 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e80901 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e80901
            | (have j0 := b8e80901 X0 X1
               grind)
            | exact resolve b8e80901 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80901
          have b8e82189 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e81685 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e81685
            | (have j0 := b8e81685 X0 X1
               grind)
            | exact resolve b8e81685 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81685
          have b8e82269 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (σ (τ X0))) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e81833 X0 X1
               have i₂ := b8e74 X0
               grind)
            | exact superpose b8e74 b8e81833
            | (have j0 := b8e81833 X0 X1
               grind)
            | exact resolve b8e81833 b8e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74 b8e81833
          have b8e82490 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k (τ (σ X0)) X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e82189 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e82189
            | (have j0 := b8e82189 X0 X1
               grind)
            | exact resolve b8e82189 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82189
          have b8e82550 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e82269 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e82269
            | (have j0 := b8e82269 X0 X1
               grind)
            | exact resolve b8e82269 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82269
          have b8e82694 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e82490 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e82490
            | (have j0 := b8e82490 X0 X1
               grind)
            | exact resolve b8e82490 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82490
          have b8e82742 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e82550 X0 X1
               have i₂ := b8e40 X0 X1
               grind)
            | exact superpose b8e40 b8e82550
            | (have j0 := b8e82550 X0 X1
               grind)
            | exact resolve b8e82550 b8e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e82550
          have b8e82801 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e82694 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e82694
            | (have j0 := b8e82694 X0 X1
               grind)
            | exact resolve b8e82694 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82694
          have b8e84345 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) (σ X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 X1
               have i₂ := b8e82801 (σ X0) X1
               grind)
            | exact superpose b8e82801 b8e37
            | (have j1 := b8e82801 (σ X0) X1
               grind)
            | exact resolve b8e37 b8e82801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82801
          have b8e84708 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (σ (M.op X0 X0))) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84345 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e84345
            | (have j0 := b8e84345 X0 X1
               grind)
            | exact resolve b8e84345 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84345
          have b8e85438 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ X1)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) ∨ (M.op X1 X1) = (k (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e84708 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e84708
            | (have j0 := b8e84708 X0 X1
               grind)
            | exact resolve b8e84708 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e84708
          have b8e103574 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10578 X1 X0
               have i₂ := b8e82742 X0 X1
               grind)
            | exact superpose b8e82742 b8e10578
            | (have j0 := b8e10578 X0 X1
               have j1 := b8e82742 X1 X0
               grind)
            | (have r₁ := b8e10578 X1 X0
               have r₂ := b8e82742 X0 X1
               grind)
            | (have r₁ := b8e10578 X1 X1
               have r₂ := b8e82742 X1 X1
               grind)
            | exact resolve b8e10578 b8e82742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e104102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17923 X1 X0
               have i₂ := b8e82742 X0 X1
               grind)
            | exact superpose b8e82742 b8e17923
            | (have j0 := b8e17923 X1 X0
               have j1 := b8e82742 X0 X1
               grind)
            | (have r₁ := b8e17923 X1 X1
               have r₂ := b8e82742 X1 X1
               grind)
            | (have r₁ := b8e17923 X1 X0
               have r₂ := b8e82742 X0 X1
               grind)
            | exact resolve b8e17923 b8e82742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17923
          have b8e104292 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e82742 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e104293 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e82742 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e82742
          have b8e104296 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e104102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104102
          have b8e104349 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e103574 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103574
          have b8e104880 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e104296 X0 X1
               have j1 := b8e18466 X1 X0
               grind)
            | (have r₁ := b8e104296 X1 X0
               have r₂ := b8e18466 X0 X1
               grind)
            | exact resolve b8e104296 b8e18466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e18466 b8e104296
          have b8e105166 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e104349 X0 X1
               have j1 := b8e104292 X0 X1
               grind)
            | (have r₁ := b8e104349 X0 X1
               have r₂ := b8e104292 X0 X1
               grind)
            | (have r₁ := b8e104349 X1 X0
               have r₂ := b8e104292 X0 X1
               grind)
            | (have r₁ := b8e104349 X1 X1
               have r₂ := b8e104292 X1 X1
               grind)
            | exact resolve b8e104349 b8e104292
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104292 b8e104349
          have b8e138788 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e104880 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e104880 X0 X1
               grind)
            | exact superpose b8e104880 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e104880 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e104880 X1 X1
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e104880 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e104880 X0 X0
               grind)
            | exact resolve b8e17 b8e104880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104880
          have b8e139561 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e138788 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138788
          have b8e139766 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e139561 X0 X1
               have j1 := b8e104293 X1 X0
               grind)
            | (have r₁ := b8e139561 X0 X1
               have r₂ := b8e104293 X0 X1
               grind)
            | (have r₁ := b8e139561 X1 X0
               have r₂ := b8e104293 X0 X1
               grind)
            | (have r₁ := b8e139561 X1 X1
               have r₂ := b8e104293 X1 X1
               grind)
            | exact resolve b8e139561 b8e104293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104293 b8e139561
          have b8e142730 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (k (σ X0) X1) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e105166 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e105166
            | (have j0 := b8e105166 (σ X0) X1
               grind)
            | exact resolve b8e105166 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105166
          have b8e144385 : ∀ X0 X1 : G, (M.op X1 X1) = (k (σ X0) X1) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (M.op X1 X1) = (M.op X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e142730 X0 X1
               have i₂ := b8e37 X0 X1
               grind)
            | exact superpose b8e37 b8e142730
            | (have j0 := b8e142730 X0 X1
               grind)
            | exact resolve b8e142730 b8e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e142730
          have b8e162756 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139766 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e139766
            | (have j0 := b8e139766 (σ X0) X1
               grind)
            | exact resolve b8e139766 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139766
          have b8e162912 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (M.op X1 X1) = (M.op (σ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e162756 X0 X1
               have i₂ := b8e30 X1 X0
               grind)
            | exact superpose b8e30 b8e162756
            | (have j0 := b8e162756 X0 X1
               grind)
            | exact resolve b8e162756 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e162756
          have b8e187445 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e85438 X1 (σ X0)
               grind)
            | exact superpose b8e85438 b8e30
            | (have j1 := b8e85438 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e85438
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e85438
          have b8e187456 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e187445 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e187445
            | (have j0 := b8e187445 X0 X1
               grind)
            | exact resolve b8e187445 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187445
          have b8e187496 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e187456 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e187456
            | (have j0 := b8e187456 X0 X1
               grind)
            | exact resolve b8e187456 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187456
          have b8e187526 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = (k X1 (τ (σ X0))) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e187496 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e187496
            | (have j0 := b8e187496 X0 X1
               grind)
            | exact resolve b8e187496 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187496
          have b8e187547 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e187526 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e187526
            | (have j0 := b8e187526 X0 X1
               grind)
            | exact resolve b8e187526 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187526
          have b8e187559 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e187547 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e187547
            | (have j0 := b8e187547 X0 X1
               grind)
            | exact resolve b8e187547 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187547
          have b8e192794 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e187559 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e187559
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e187559 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e192804 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e187559 x y
               grind)
            | exact superpose b8e187559 b8e20
            | (have j1 := b8e187559 x y
               grind)
            | exact resolve b8e20 b8e187559
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e187559
          have b8e192973 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e192794 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192794
          have b8e194221 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e192804
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e192804
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e192804 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e194226 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e192804
               have i₂ := b8e5507 x y
               grind)
            | exact superpose b8e5507 b8e192804
            | (have j1 := b8e5507 x y
               grind)
            | (have r₁ := b8e192804
               have r₂ := b8e5507 x y
               grind)
            | exact resolve b8e192804 b8e5507
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5507 b8e192804
          have b8e194233 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e194226
          have b8e194234 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e194233
          have b8e194239 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e194221
          have b8e194240 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e194239
          have b8e194242 : (M.op y y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e16 y x
               grind)
            | (have r₁ := b8e194234
               have r₂ := b8e16 y x
               grind)
            | exact resolve b8e194234 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194234
          have b8e198236 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e10578 y x
               have i₂ := b8e194242
               grind)
            | exact superpose b8e194242 b8e10578
            | (have j0 := b8e10578 y x
               grind)
            | (have r₁ := b8e10578 y x
               have r₂ := b8e194242
               grind)
            | exact resolve b8e10578 b8e194242
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10578
          have b8e198253 : (M.op x x) ≠ (M.op y y) ∨ (M.op x x) = (k y x) := by grind
          clear b8e194242
          have b8e198257 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k y x) := by grind
          clear b8e198236
          have b8e198273 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b8e198257
               have r₂ := b8e198253
               grind)
            | exact resolve b8e198257 b8e198253
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e198253 b8e198257
          have b8e216023 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e192973 X0 X1
               grind)
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e192973 X0 X1
               grind)
            | exact superpose b8e192973 b8e17
            | (have j0 := b8e17 X1 X0
               have j1 := b8e192973 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e192973 X1 X1
               grind)
            | (have r₁ := b8e17 X1 X0
               have r₂ := b8e192973 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e192973 X0 X0
               grind)
            | exact resolve b8e17 b8e192973
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e216090 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e192973 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192973
          have b8e216102 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e216023 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216023
          have b8e216126 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e216102 X0 X1
               have j1 := b8e216090 X0 X1
               grind)
            | (have r₁ := b8e216102 X0 X1
               have r₂ := b8e216090 X0 X1
               grind)
            | (have r₁ := b8e216102 X1 X0
               have r₂ := b8e216090 X0 X1
               grind)
            | (have r₁ := b8e216102 X1 X1
               have r₂ := b8e216090 X1 X1
               grind)
            | exact resolve b8e216102 b8e216090
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216090 b8e216102
          have b8e240235 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e216126 x y
               grind)
            | exact superpose b8e216126 b8e20
            | (have j1 := b8e216126 x y
               grind)
            | (have r₁ := b8e20
               have r₂ := b8e216126 x y
               grind)
            | exact resolve b8e20 b8e216126
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e216126
          have b8e240266 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e240235
          have b8e241870 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e16260 y x
               have i₂ := b8e240266
               grind)
            | exact superpose b8e240266 b8e16260
            | (have j0 := b8e16260 y x
               grind)
            | exact resolve b8e16260 b8e240266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e16260
          have b8e241898 : (M.op x x) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e241870
          have b8e309763 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X1)) X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 (σ X1) X0
               have i₂ := b8e144385 X1 (σ X0)
               grind)
            | exact superpose b8e144385 b8e30
            | (have j1 := b8e144385 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e144385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e144385
          have b8e309768 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e309763 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e309763
            | (have j0 := b8e309763 X0 X1
               grind)
            | exact resolve b8e309763 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309763
          have b8e309781 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e309768 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e309768
            | (have j0 := b8e309768 X0 X1
               grind)
            | exact resolve b8e309768 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309768
          have b8e309788 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 (τ (σ X0))) = (M.op (τ (σ X0)) X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e309781 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e309781
            | (have j0 := b8e309781 X0 X1
               grind)
            | exact resolve b8e309781 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309781
          have b8e309792 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e309788 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e309788
            | (have j0 := b8e309788 X0 X1
               grind)
            | exact resolve b8e309788 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309788
          have b8e309793 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e309792 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e309792
            | (have j0 := b8e309792 X0 X1
               grind)
            | exact resolve b8e309792 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309792
          have b8e309950 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (M.op x y) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e309793 x y
               grind)
            | exact superpose b8e309793 b8e20
            | (have j1 := b8e309793 x y
               grind)
            | exact resolve b8e20 b8e309793
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309793
          have b8e343255 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (M.op (σ X0) (σ X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e37 X0 (σ X1)
               have i₂ := b8e162912 X1 (σ X0)
               grind)
            | exact superpose b8e162912 b8e37
            | (have j1 := b8e162912 X1 (σ X0)
               grind)
            | exact resolve b8e37 b8e162912
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e37 b8e162912
          have b8e343260 : ∀ X0 X1 : G, (k X0 (τ (σ X1))) = (τ (σ (M.op X0 X0))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e343255 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e343255
            | (have j0 := b8e343255 X0 X1
               grind)
            | exact resolve b8e343255 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343255
          have b8e343277 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e343260 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e343260
            | (have j0 := b8e343260 X0 X1
               grind)
            | exact resolve b8e343260 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343260
          have b8e343288 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (M.op X1 (τ (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e343277 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e343277
            | (have j0 := b8e343277 X0 X1
               grind)
            | exact resolve b8e343277 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343277
          have b8e343294 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e343288 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e343288
            | (have j0 := b8e343288 X0 X1
               grind)
            | exact resolve b8e343288 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343288
          have b8e343295 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e343294 X0 X1
               have i₂ := b8e71 X0
               grind)
            | exact superpose b8e71 b8e343294
            | (have j0 := b8e343294 X0 X1
               grind)
            | exact resolve b8e343294 b8e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71 b8e343294
          have b8e348898 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (k y x) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e343295 y x
               grind)
            | exact superpose b8e343295 b8e20
            | (have j1 := b8e343295 y x
               grind)
            | exact resolve b8e20 b8e343295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343295
          have b8e353694 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e348898
               have i₂ := b8e194240
               grind)
            | exact superpose b8e194240 b8e348898
            | exact resolve b8e348898 b8e194240
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194240 b8e348898
          have b8e353695 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e353694
          have b8e353696 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e353695
          have b8e358500 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e198273
               have i₂ := b8e353696
               grind)
            | exact superpose b8e353696 b8e198273
            | exact resolve b8e198273 b8e353696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e198273 b8e353696
          have b8e358541 : (M.op x y) = (M.op x x) := by grind
          clear b8e358500
          have b8e363406 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e309950
               have i₂ := b8e358541
               grind)
            | exact superpose b8e358541 b8e309950
            | exact resolve b8e309950 b8e358541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e309950
          have b8e363456 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op x x) = (k y x) := by grind
          clear b8e363406
          have b8e363457 : (M.op x x) = (k y x) := by grind
          clear b8e363456
          have b8e368449 : (M.op x x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e240266
               have i₂ := b8e363457
               grind)
            | exact superpose b8e363457 b8e240266
            | exact resolve b8e240266 b8e363457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e240266
          have b8e368518 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e1379 x y
               have i₂ := b8e363457
               grind)
            | exact superpose b8e363457 b8e1379
            | (have j0 := b8e1379 x y
               grind)
            | exact resolve b8e1379 b8e363457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1379 b8e363457
          have b8e368551 : (σ (M.op y y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e368518
          have b8e368599 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e368449
               have r₂ := b8e241898
               grind)
            | exact resolve b8e368449 b8e241898
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e241898 b8e368449
          have b8e368616 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b8e368599
               have i₂ := b8e358541
               grind)
            | exact superpose b8e358541 b8e368599
            | exact resolve b8e368599 b8e358541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368599
          have b8e428064 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b8e368551
               have i₂ := b8e368616
               grind)
            | exact superpose b8e368616 b8e368551
            | exact resolve b8e368551 b8e368616
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368551 b8e368616
          have b8e428066 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
          clear b8e428064
          have b8e428814 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e428066
               grind)
            | exact superpose b8e428066 b8e20
            | exact resolve b8e20 b8e428066
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e428066
          have b8e428876 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e428814
               have i₂ := b8e358541
               grind)
            | exact superpose b8e358541 b8e428814
            | exact resolve b8e428814 b8e358541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e358541 b8e428814
          have b8e428877 : False := by grind
          exact b8e428877

/-- `Equation677`: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation677 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law677 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law677.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e75 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e81 : False := by grind
      exact b0e81
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op x x) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : (M.op x x) = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e65 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ y = X0 ∨ (k X0 y) = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e17
            | (have j0 := b4e17 X0 x
               grind)
            | (have r₁ := b4e17 x y
               have r₂ := b4e22
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e22
               grind)
            | exact resolve b4e17 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e66 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e17 X0 (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e17
            | (have j0 := b4e17 X0 (σ x)
               grind)
            | (have r₁ := b4e17 (σ x) (σ y)
               have r₂ := b4e24
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e24
               grind)
            | exact resolve b4e17 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e69 : ∀ X0 : G, (M.op X0 X0) ≠ (σ (M.op x x)) ∨ (σ y) = X0 ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e66 X0
               have i₂ := b4e30 x
               grind)
            | exact superpose b4e30 b4e66
            | (have j0 := b4e66 X0
               grind)
            | exact resolve b4e66 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e199 : x = y ∨ (M.op x y) = (k x y) := by
            first
            | (have j0 := b4e65 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e200 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e199
               have r₂ := b4e21
               grind)
            | exact resolve b4e199 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e199
          have b4e394 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ X0) = (σ y) ∨ (k (σ X0) (σ y)) = (M.op (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e69 (σ X0)
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e69
            | (have j0 := b4e69 (σ X0)
               grind)
            | (have r₁ := b4e69 (σ x)
               have r₂ := b4e30 x
               grind)
            | exact resolve b4e69 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e69
          have b4e402 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ X0) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e394 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e394
            | (have j0 := b4e394 X0
               grind)
            | exact resolve b4e394 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e394
          have b4e10415 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b4e402 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e402
          have b4e10422 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b4e10415
               have r₂ := b4e23
               grind)
            | exact resolve b4e10415 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10415
          have b4e10436 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e10422
               have i₂ := b4e200
               grind)
            | exact superpose b4e200 b4e10422
            | exact resolve b4e10422 b4e200
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e200 b4e10422
          have b4e10447 : False := by grind
          exact b4e10447
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : (M.op x x) = (M.op y y) := by grind
          have b5e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e55 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e30 y
               grind)
            | exact superpose b5e30 b5e24
            | exact resolve b5e24 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e57 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e55
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e55
            | exact resolve b5e55 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e55
          have b5e58 : False := by grind
          exact b5e58
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
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e57 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e24
            | exact resolve b7e24 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e59 : (σ (M.op x x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e57
               have i₂ := b7e30 x
               grind)
            | exact superpose b7e30 b7e57
            | exact resolve b7e57 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e57
          have b7e71 : (M.op y y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e59
               grind)
            | exact superpose b7e59 b7e14
            | exact resolve b7e14 b7e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e72 : (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e71
            | exact resolve b7e71 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e76 : False := by grind
          exact b7e76
        · have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e22 : (M.op x x) ≠ (M.op y y) := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          have b8e24 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e54 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e56 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e54
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e54
            | exact resolve b8e54 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e68 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e76 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k y X0) ∨ y = X0 := by
            intro X0
            first
            | (have i₁ := b8e22
               have i₂ := b8e18 y X0
               grind)
            | (have i₁ := b8e22
               have i₂ := b8e18 X0 y
               grind)
            | exact superpose b8e18 b8e22
            | (have j1 := b8e18 y X0
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e22
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e22 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e68 X0 X1
               have i₂ := b8e30 X1
               grind)
            | exact superpose b8e30 b8e68
            | (have j0 := b8e68 X0 X1
               grind)
            | exact resolve b8e68 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e88 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e86 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e86
            | (have j0 := b8e86 X0 X1
               grind)
            | exact resolve b8e86 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e86
          have b8e109 : (M.op x y) = (k y x) ∨ x = y := by
            first
            | (have j0 := b8e76 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e110 : (M.op x y) = (k y x) := by
            first
            | (have r₁ := b8e109
               have r₂ := b8e21
               grind)
            | exact resolve b8e109 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e293 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e88 x y
               grind)
            | exact superpose b8e88 b8e20
            | (have j1 := b8e88 y x
               grind)
            | exact resolve b8e20 b8e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e339 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e293
               have r₂ := b8e56
               grind)
            | exact resolve b8e293 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56 b8e293
          have b8e354 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have r₁ := b8e339
               have r₂ := b8e23
               grind)
            | exact resolve b8e339 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339
          have b8e365 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e354
               have i₂ := b8e110
               grind)
            | exact superpose b8e110 b8e354
            | exact resolve b8e354 b8e110
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110 b8e354
          have b8e366 : False := by grind
          exact b8e366

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation854 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e20 : x = y := by grind
        have b1e21 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : False := by grind
        exact b1e27
      · have b2e20 : x = y := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : False := by grind
        exact b2e27
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e29
          have b4e49 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k X0 (τ X1))
               have i₂ := b4e27 X1 X0
               grind)
            | exact superpose b4e27 b4e14
            | exact resolve b4e14 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X1 X0
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e17 X1 X1
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e82 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82
          have b4e92 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e91 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e91
          have b4e95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e79 X0 X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e79
            | (have j0 := b4e79 X0 X1
               grind)
            | exact resolve b4e79 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e79
          have b4e351 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e92 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92
          have b4e353 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e351 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e351 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e351 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | (have r₁ := b4e351 X0 X1
               have r₂ := b4e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b4e351 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e351
          have b4e374 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X0 X1
               have i₂ := b4e353 X1 (τ X0)
               grind)
            | exact superpose b4e353 b4e27
            | (have j1 := b4e353 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b4e27 b4e353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27
          have b4e376 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e49 X1 X0
               have i₂ := b4e353 (σ X1) X0
               grind)
            | exact superpose b4e353 b4e49
            | (have j1 := b4e353 (k X1 (τ X0)) (τ (M.op X0 (σ X1)))
               grind)
            | exact resolve b4e49 b4e353
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e353
          have b4e837 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e95 x y
               grind)
            | exact superpose b4e95 b4e20
            | (have j1 := b4e95 x y
               grind)
            | exact resolve b4e20 b4e95
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e95
          have b4e905 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e837
               have r₂ := b4e23
               grind)
            | exact resolve b4e837 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e837
          have b4e3694 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e374 (σ X0) X1
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e374
            | exact resolve b4e374 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e374
          have b4e3809 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e3694 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e3694
            | (have j0 := b4e3694 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b4e3694 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3694
          have b4e6537 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e905
               have i₂ := b4e3809 x y
               grind)
            | exact superpose b4e3809 b4e905
            | (have j1 := b4e3809 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b4e905
               have r₂ := b4e3809 x y
               grind)
            | (have r₁ := b4e905
               have r₂ := b4e3809 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e905
               have r₂ := b4e3809 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e905 b4e3809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e905
          have b4e6538 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b4e6537
          have b4e6543 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e6538
               have r₂ := b4e21
               grind)
            | exact resolve b4e6538 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6538
          have b4e6549 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e6543
               grind)
            | exact superpose b4e6543 b4e20
            | exact resolve b4e20 b4e6543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6553 : (τ (σ (M.op x x))) = (k y (τ (σ x))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e376 (σ x) y
               have i₂ := b4e6543
               grind)
            | exact superpose b4e6543 b4e376
            | (have j0 := b4e376 (σ y) x
               grind)
            | exact resolve b4e376 b4e6543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e376 b4e6543
          have b4e6596 : (τ (σ (M.op x x))) = (k y (τ (σ x))) := by
            first
            | (have r₁ := b4e6553
               have r₂ := b4e23
               grind)
            | exact resolve b4e6553 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6553
          have b4e6599 : (k y x) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b4e6596
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e6596
            | exact resolve b4e6596 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6596
          have b4e6601 : (M.op x x) = (k y x) := by
            first
            | (have i₁ := b4e6599
               have i₂ := b4e14 (M.op x x)
               grind)
            | exact superpose b4e14 b4e6599
            | exact resolve b4e6599 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6599
          have b4e6697 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b4e3809 x y
               have i₂ := b4e6601
               grind)
            | exact superpose b4e6601 b4e3809
            | (have j0 := b4e3809 (σ (M.op x y)) (σ (M.op x x))
               grind)
            | exact resolve b4e3809 b4e6601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3809 b4e6601
          have b4e6700 : x = y := by
            first
            | (have r₁ := b4e6697
               have r₂ := b4e6549
               grind)
            | exact resolve b4e6697 b4e6549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6549 b4e6697
          have b4e6706 : False := by grind
          exact b4e6706
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          have b5e24 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e29
          have b5e59 : (M.op y y) ≠ (M.op y y) ∨ x = y ∨ (M.op y y) = (k x y) := by
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
          have b5e63 : x = y ∨ (M.op y y) = (k x y) := by grind
          clear b5e59
          have b5e64 : (M.op y y) = (k x y) := by
            first
            | (have r₁ := b5e63
               have r₂ := b5e21
               grind)
            | exact resolve b5e63 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63
          have b5e70 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e86 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e70 X0 X1
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e70
            | (have j0 := b5e70 X0 X1
               grind)
            | exact resolve b5e70 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e668 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e86 y x
               grind)
            | exact superpose b5e86 b5e24
            | (have j1 := b5e86 y x
               grind)
            | exact resolve b5e24 b5e86
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e728 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e668
               have r₂ := b5e23
               grind)
            | exact resolve b5e668 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e668
          have b5e742 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b5e728
               have i₂ := b5e64
               grind)
            | exact superpose b5e64 b5e728
            | exact resolve b5e728 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e728
          have b5e748 : (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
            first
            | (have r₁ := b5e742
               have r₂ := b5e30 y
               grind)
            | exact resolve b5e742 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e742
          have b5e752 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e748
               grind)
            | exact superpose b5e748 b5e24
            | exact resolve b5e24 b5e748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e748
          have b5e769 : False := by grind
          exact b5e769
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : (M.op y x) ≠ (M.op y y) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e29
          have b7e62 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
          have b7e65 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
          clear b7e62
          have b7e66 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e65
               have r₂ := b7e23
               grind)
            | exact resolve b7e65 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
          have b7e68 : (σ (M.op y y)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e67
            | exact resolve b7e67 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e67
          have b7e72 : (k x y) = (τ (σ (M.op y y))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e14
            | exact resolve b7e14 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e73 : (M.op y y) = (k x y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e14 (M.op y y)
               grind)
            | exact superpose b7e14 b7e72
            | exact resolve b7e72 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e100 : (M.op y x) = (M.op y y) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e73
               grind)
            | exact superpose b7e73 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e101 : (M.op y x) = (M.op y y) ∨ x = y := by grind
          clear b7e100
          have b7e103 : x = y := by
            first
            | (have r₁ := b7e101
               have r₂ := b7e22
               grind)
            | exact resolve b7e101 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101
          have b7e105 : False := by grind
          exact b7e105
        · have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
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
          have b8e36 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          clear b8e26
          have b8e77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e79 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e17 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X0
               have j1 := b8e18 X1 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e79 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e89 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e88 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e90 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e77
            | (have j0 := b8e77 X0 X1
               grind)
            | exact resolve b8e77 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e77
          have b8e206 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e89 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e89
          have b8e208 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have j0 := b8e206 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e206 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e206 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | (have r₁ := b8e206 X0 X1
               have r₂ := b8e18 (M.op X1 X0) (M.op X1 X1)
               grind)
            | exact resolve b8e206 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e206
          have b8e267 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e36 X1 X0
               have i₂ := b8e208 X1 (σ X0)
               grind)
            | exact superpose b8e208 b8e36
            | (have j1 := b8e208 (k (τ X1) X0) (τ (M.op (σ X0) X1))
               grind)
            | exact resolve b8e36 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e268 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e27 X0 X1
               have i₂ := b8e208 X1 (τ X0)
               grind)
            | exact superpose b8e208 b8e27
            | (have j1 := b8e208 (k (σ X1) X0) (σ (M.op (τ X0) X1))
               grind)
            | exact resolve b8e27 b8e208
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27 b8e208
          have b8e578 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e90 x y
               grind)
            | exact superpose b8e90 b8e20
            | (have j1 := b8e90 x y
               grind)
            | exact resolve b8e20 b8e90
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e90
          have b8e640 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e578
               have r₂ := b8e23
               grind)
            | exact resolve b8e578 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e578
          have b8e3301 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e268 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e268
            | exact resolve b8e268 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e268
          have b8e3400 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e3301 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e3301
            | (have j0 := b8e3301 (σ (k X1 X0)) (σ (M.op X0 X1))
               grind)
            | exact resolve b8e3301 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3301
          have b8e3657 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e640
               have i₂ := b8e3400 x y
               grind)
            | exact superpose b8e3400 b8e640
            | (have j1 := b8e3400 (M.op (σ x) (σ y)) (σ (M.op x x))
               grind)
            | (have r₁ := b8e640
               have r₂ := b8e3400 x y
               grind)
            | (have r₁ := b8e640
               have r₂ := b8e3400 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e640
               have r₂ := b8e3400 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e640 b8e3400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e640
          have b8e3658 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = y := by grind
          clear b8e3657
          have b8e3663 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e3658
               have r₂ := b8e21
               grind)
            | exact resolve b8e3658 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3658
          have b8e3669 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3663
               grind)
            | exact superpose b8e3663 b8e20
            | exact resolve b8e20 b8e3663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3670 : (k (τ (σ y)) x) = (τ (σ (M.op x x))) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e267 x (σ y)
               have i₂ := b8e3663
               grind)
            | exact superpose b8e3663 b8e267
            | (have j0 := b8e267 x (σ y)
               grind)
            | exact resolve b8e267 b8e3663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e267 b8e3663
          have b8e3713 : (k (τ (σ y)) x) = (τ (σ (M.op x x))) := by
            first
            | (have r₁ := b8e3670
               have r₂ := b8e23
               grind)
            | exact resolve b8e3670 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3670
          have b8e3714 : (M.op x x) = (k (τ (σ y)) x) := by
            first
            | (have i₁ := b8e3713
               have i₂ := b8e14 (M.op x x)
               grind)
            | exact superpose b8e14 b8e3713
            | exact resolve b8e3713 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3713
          have b8e3715 : (k y x) = (M.op x x) := by
            first
            | (have i₁ := b8e3714
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e3714
            | exact resolve b8e3714 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3714
          have b8e3736 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = y := by
            first
            | (have i₁ := b8e3400 x y
               have i₂ := b8e3715
               grind)
            | exact superpose b8e3715 b8e3400
            | (have j0 := b8e3400 (σ (M.op x y)) (σ (M.op x x))
               grind)
            | exact resolve b8e3400 b8e3715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3400 b8e3715
          have b8e3739 : x = y := by
            first
            | (have r₁ := b8e3736
               have r₂ := b8e3669
               grind)
            | exact resolve b8e3736 b8e3669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3669 b8e3736
          have b8e3745 : False := by grind
          exact b8e3745
