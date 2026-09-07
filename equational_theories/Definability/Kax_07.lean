import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pxy_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
      have b0e43 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e44 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e48 : (M.op x x) = (k x y) := by grind
      clear b0e44
      have b0e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e43
      have b0e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e49
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e49
        | exact resolve b0e49 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e53 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e52
           have i₂ := b0e48
           grind)
        | exact superpose b0e48 b0e52
        | exact resolve b0e52 b0e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48 b0e52
      have b0e54 : False := by grind
      exact b0e54
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
        have b1e27 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x x))) := by
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
        have b1e32 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e27 x
             have i₂ := b1e12 x x x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e61 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
          | (have i₁ := b1e61
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e61
          | exact resolve b1e61 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e61
        have b1e63 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e62
          | exact resolve b1e62 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e62
        have b1e64 : False := by grind
        exact b1e64
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
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e55 : (M.op x x) = (k x y) := by grind
        clear b2e48
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
        have b2e113 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e3015 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e113 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e113
        have b2e3016 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e3015
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e3015
          | exact resolve b2e3015 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3015
        have b2e3019 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e3016
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e3016
          | exact resolve b2e3016 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e3016
        have b2e3020 : False := by grind
        exact b2e3020
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
        have b3e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e44 x
             have i₂ := b3e12 (σ x) (σ x) x
             grind)
          | exact superpose b3e12 b3e44
          | exact resolve b3e44 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e195 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e15
          | (have j0 := b3e15 (σ x) (σ x)
             grind)
          | exact resolve b3e15 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e197 : (M.op (σ x) (σ x)) = (k (σ y) (σ y)) := by grind
        clear b3e195
        have b3e199 : (M.op (σ x) (σ x)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e197
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e197
          | exact resolve b3e197 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197
        have b3e205 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e199
             have i₂ := b3e60 y
             grind)
          | exact superpose b3e60 b3e199
          | exact resolve b3e199 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e199
        have b3e210 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e205
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e205
          | exact resolve b3e205 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e205
        have b3e213 : False := by grind
        exact b3e213
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
          have b4e72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e74 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e72
          have b4e77 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e74
            | exact resolve b4e74 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e79 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e73 y
               grind)
            | exact superpose b4e73 b4e77
            | exact resolve b4e77 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e77
          have b4e80 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e79
            | exact resolve b4e79 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e81 : False := by grind
          exact b4e81
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
          have b5e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e70 (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e75 X0
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e75
            | exact resolve b5e75 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e75
          have b5e92 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e128 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
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
          have b5e146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e148 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e128 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e128
          have b5e151 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e146 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e146 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e146 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e146 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e146
          have b5e156 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e138 X0
               have j1 := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e138 X0
               have r₂ := b5e16 X0 (σ y)
               grind)
            | (have r₁ := b5e138 (σ y)
               have r₂ := b5e16 (σ y) (σ y)
               grind)
            | exact resolve b5e138 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e138
          have b5e164 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e148 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e148 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | (have r₁ := b5e148 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e148 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e148
          have b5e180 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e164 X0 X1
               have j1 := b5e151 X1 X0
               grind)
            | (have r₁ := b5e164 X0 X1
               have r₂ := b5e151 X0 X1
               grind)
            | (have r₁ := b5e164 X1 X0
               have r₂ := b5e151 X0 X1
               grind)
            | exact resolve b5e164 b5e151
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e151 b5e164
          have b5e855 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b5e180 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e180
          have b5e3819 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e156 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e156
          have b5e3820 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e3819
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e3819
            | exact resolve b5e3819 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3819
          have b5e3888 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e92 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e3889 : (M.op x x) = (k x y) := by
            first
            | (have j1 := b5e855 x y
               grind)
            | (have r₁ := b5e3888
               have r₂ := b5e855 x y
               grind)
            | exact resolve b5e3888 b5e855
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e855 b5e3888
          have b5e3951 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e3820
               grind)
            | exact superpose b5e3820 b5e23
            | exact resolve b5e23 b5e3820
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3820
          have b5e3978 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3951
               have i₂ := b5e3889
               grind)
            | exact superpose b5e3889 b5e3951
            | exact resolve b5e3951 b5e3889
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3889 b5e3951
          have b5e3990 : False := by grind
          exact b5e3990
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
        have b6e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e58 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e56
        have b6e60 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e77 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e23
          | exact resolve b6e23 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e60
        have b6e162 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
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
        have b6e163 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
        clear b6e162
        have b6e164 : (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e163
             have r₂ := b6e20
             grind)
          | exact resolve b6e163 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e163
        have b6e165 : False := by grind
        exact b6e165
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
          have b7e65 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e16 X2 X3
               have i₂ := b7e13 X2 X0 X1
               grind)
            | exact superpose b7e13 b7e16
            | (have j0 := b7e16 X2 X3
               grind)
            | (have r₁ := b7e16 X1 (M.op X2 (M.op X1 X1))
               have r₂ := b7e13 X1 X1 X2
               grind)
            | exact resolve b7e16 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e69 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e69
          have b7e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e70 y
               grind)
            | exact superpose b7e70 b7e73
            | exact resolve b7e73 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e70 (σ X0)
               grind)
            | exact superpose b7e70 b7e19
            | exact resolve b7e19 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e76 X0
               have i₂ := b7e70 X0
               grind)
            | exact superpose b7e70 b7e76
            | exact resolve b7e76 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e76
          have b7e94 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e96 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e94 X0
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e94
            | (have j0 := b7e94 X0
               grind)
            | exact resolve b7e94 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e97 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e23
            | exact resolve b7e23 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e97
            | exact resolve b7e97 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e117 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 (M.op X2 X0))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X0 X2 X3
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X1 X1 X2
               have i₂ := b7e18 X1 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e163 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e117 X0 X1 x x
               have j1 := b7e65 X0 X1 X0 X1
               grind)
            | (have r₁ := b7e117 X0 (M.op X1 (M.op X0 x)) x x
               have r₂ := b7e65 X0 X1 x (M.op x (M.op x X0))
               grind)
            | (have r₁ := b7e117 x x X0 X1
               have r₂ := b7e65 X0 X1 x x
               grind)
            | exact resolve b7e117 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e117
          have b7e6500 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e96 (σ x)
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e96
            | (have j0 := b7e96 (σ x)
               grind)
            | (have r₁ := b7e96 (σ x)
               have r₂ := b7e74
               grind)
            | exact resolve b7e96 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e96
          have b7e6501 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e6500
          have b7e6503 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e6501
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e6501
            | exact resolve b7e6501 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6501
          have b7e6504 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e6503
               have r₂ := b7e103
               grind)
            | exact resolve b7e6503 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103 b7e6503
          have b7e6505 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e6504
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e6504
            | exact resolve b7e6504 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6504
          have b7e6506 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e6505
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e6505
            | exact resolve b7e6505 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e6505
          have b7e6513 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e6506
               grind)
            | exact superpose b7e6506 b7e14
            | exact resolve b7e14 b7e6506
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6506
          have b7e6526 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e6513
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e6513
            | exact resolve b7e6513 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6513
          have b7e6847 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e163 x y
               have i₂ := b7e6526
               grind)
            | exact superpose b7e6526 b7e163
            | (have j0 := b7e163 x y
               grind)
            | exact resolve b7e163 b7e6526
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e163 b7e6526
          have b7e6854 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e6847
               have r₂ := b7e21
               grind)
            | exact resolve b7e6847 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e6847
          have b7e6862 : False := by grind
          exact b7e6862
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
          have b8e64 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X2 X3) ∨ (M.op X2 X3) = (k X2 X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e16 X2 X3
               have i₂ := b8e13 X2 X0 X1
               grind)
            | exact superpose b8e13 b8e16
            | (have j0 := b8e16 X2 X3
               grind)
            | (have r₁ := b8e16 X1 (M.op X2 (M.op X1 X1))
               have r₂ := b8e13 X1 X1 X2
               grind)
            | exact resolve b8e16 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e112 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X2 (M.op X3 (M.op X2 X0))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X0 X2 X3
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X1 X1 X2
               have i₂ := b8e18 X1 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
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
          have b8e149 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b8e131 X0
               have j1 := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e131 X0
               have r₂ := b8e16 X0 (σ y)
               grind)
            | (have r₁ := b8e131 (σ y)
               have r₂ := b8e16 (σ y) (σ y)
               grind)
            | exact resolve b8e131 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e161 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e112 X0 X1 x x
               have j1 := b8e64 X0 X1 X0 X1
               grind)
            | (have r₁ := b8e112 X0 (M.op X1 (M.op X0 x)) x x
               have r₂ := b8e64 X0 X1 x (M.op x (M.op x X0))
               grind)
            | (have r₁ := b8e112 x x X0 X1
               have r₂ := b8e64 X0 X1 x x
               grind)
            | exact resolve b8e112 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64 b8e112
          have b8e3432 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e149 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e149
          have b8e3433 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e3432
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e3432
            | exact resolve b8e3432 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3432
          have b8e3438 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3433
               grind)
            | exact superpose b8e3433 b8e20
            | exact resolve b8e20 b8e3433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3433
          have b8e3512 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e3438
               have i₂ := b8e161 x y
               grind)
            | exact superpose b8e161 b8e3438
            | (have j1 := b8e161 x y
               grind)
            | exact resolve b8e3438 b8e161
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e161 b8e3438
          have b8e3515 : (M.op x y) = (M.op y y) := by grind
          clear b8e3512
          have b8e3518 : False := by grind
          exact b8e3518

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3292 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
      have b0e56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e59 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e56 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e56
        | exact resolve b0e56 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e56
      have b0e179 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e59 x
           grind)
        | exact superpose b0e59 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e59 x
           grind)
        | exact resolve b0e22 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e59
      have b0e190 : False := by grind
      exact b0e190
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
        have b1e27 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x x))) := by
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
        have b1e32 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e27 x
             have i₂ := b1e12 x x x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e52 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        have b1e58 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e62 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
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
        have b1e63 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e55 y
             grind)
          | exact superpose b1e55 b1e62
          | exact resolve b1e62 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e62
        have b1e64 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e63
             have i₂ := b1e32
             grind)
          | exact superpose b1e32 b1e63
          | exact resolve b1e63 b1e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32 b1e63
        have b1e65 : False := by grind
        exact b1e65
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X1) := by
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
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b2e27 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op x x))) := by
          intro X0
          first
          | (have i₁ := b2e12 y x X0
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e27 x
             have i₂ := b2e12 x x x
             grind)
          | exact superpose b2e12 b2e27
          | exact resolve b2e27 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b2e55 : (M.op y y) = (k x y) := by grind
        clear b2e48
        have b2e57 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e55
             have i₂ := b2e32
             grind)
          | exact superpose b2e32 b2e55
          | exact resolve b2e55 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32 b2e55
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
        have b2e5945 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e99 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e99
        have b2e5946 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e5945
             have r₂ := b2e21
             grind)
          | exact resolve b2e5945 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5945
        have b2e5948 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e5946
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e5946
          | exact resolve b2e5946 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5946
        have b2e5950 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e5948
             have i₂ := b2e57
             grind)
          | exact superpose b2e57 b2e5948
          | exact resolve b2e5948 b2e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57 b2e5948
        have b2e5951 : False := by grind
        exact b2e5951
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
        have b3e44 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b3e12 (σ y) (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e44 x
             have i₂ := b3e12 (σ x) (σ x) x
             grind)
          | exact superpose b3e12 b3e44
          | exact resolve b3e44 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e59 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e60 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e61 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e59
        have b3e64 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e61
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e61
          | exact resolve b3e61 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61
        have b3e85 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e64
             grind)
          | exact superpose b3e64 b3e15
          | exact resolve b3e15 b3e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e87 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e85
        have b3e88 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e87
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e87
          | exact resolve b3e87 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e89 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e60 y
             grind)
          | exact superpose b3e60 b3e88
          | exact resolve b3e88 b3e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e60 b3e88
        have b3e90 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e89
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e89
          | exact resolve b3e89 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e89
        have b3e168 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e64
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e64
          | exact resolve b3e64 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45 b3e64
        have b3e181 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e168
             have i₂ := b3e90
             grind)
          | exact superpose b3e90 b3e168
          | exact resolve b3e168 b3e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90 b3e168
        have b3e185 : False := by grind
        exact b3e185
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
          have b4e72 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e73 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e74 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e72
          have b4e77 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e74
            | exact resolve b4e74 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e79 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e77
               have i₂ := b4e73 y
               grind)
            | exact superpose b4e73 b4e77
            | exact resolve b4e77 b4e73
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e73 b4e77
          have b4e80 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e79
            | exact resolve b4e79 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e79
          have b4e81 : False := by grind
          exact b4e81
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
          have b5e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e75 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e70 (σ X0)
               grind)
            | exact superpose b5e70 b5e19
            | exact resolve b5e19 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e75 X0
               have i₂ := b5e70 X0
               grind)
            | exact superpose b5e70 b5e75
            | exact resolve b5e75 b5e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70 b5e75
          have b5e92 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e2171 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e92 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e92
          have b5e2172 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e2171
               have r₂ := b5e21
               grind)
            | exact resolve b5e2171 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2171
          have b5e7201 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e138 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e138
          have b5e7202 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e7201
               have r₂ := b5e23
               grind)
            | exact resolve b5e7201 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7201
          have b5e7204 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e7202
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e7202
            | exact resolve b5e7202 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7202
          have b5e7206 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e7204
               have i₂ := b5e2172
               grind)
            | exact superpose b5e2172 b5e7204
            | exact resolve b5e7204 b5e2172
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2172 b5e7204
          have b5e7209 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e7206
               grind)
            | exact superpose b5e7206 b5e23
            | exact resolve b5e23 b5e7206
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e7206
          have b5e7252 : False := by grind
          exact b5e7252
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
          intro X0 X1 X2
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
        have b6e43 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ x)))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ y) (σ x) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e43 x
             have i₂ := b6e12 (σ x) (σ x) x
             grind)
          | exact superpose b6e12 b6e43
          | exact resolve b6e43 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e56 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e57 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e58 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e56
        have b6e60 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e58
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e58
          | exact resolve b6e58 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e79 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e60
             grind)
          | exact superpose b6e60 b6e15
          | exact resolve b6e15 b6e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
             have i₂ := b6e57 y
             grind)
          | exact superpose b6e57 b6e82
          | exact resolve b6e82 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e57 b6e82
        have b6e140 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e83
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e83
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e83 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e149 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e140
             have r₂ := b6e20
             grind)
          | exact resolve b6e140 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e140
        have b6e150 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b6e149
             have r₂ := b6e21
             grind)
          | exact resolve b6e149 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e154 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e60
             have i₂ := b6e44
             grind)
          | exact superpose b6e44 b6e60
          | exact resolve b6e60 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44 b6e60
        have b6e167 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e154
             have i₂ := b6e83
             grind)
          | exact superpose b6e83 b6e154
          | exact resolve b6e154 b6e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e83 b6e154
        have b6e171 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e167
             have i₂ := b6e150
             grind)
          | exact superpose b6e150 b6e167
          | exact resolve b6e167 b6e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e150 b6e167
        have b6e174 : False := by grind
        exact b6e174
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b7e69 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e71 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e69
          have b7e73 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e71
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e71
            | exact resolve b7e71 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e71
          have b7e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e73
               have i₂ := b7e70 y
               grind)
            | exact superpose b7e70 b7e73
            | exact resolve b7e73 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e73
          have b7e76 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e70 (σ X0)
               grind)
            | exact superpose b7e70 b7e19
            | exact resolve b7e19 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e85 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e76 X0
               have i₂ := b7e70 X0
               grind)
            | exact superpose b7e70 b7e76
            | exact resolve b7e76 b7e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70 b7e76
          have b7e94 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e96 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e94 X0
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e94
            | (have j0 := b7e94 X0
               grind)
            | exact resolve b7e94 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e97 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e23
            | exact resolve b7e23 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e103 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e97
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e97
            | exact resolve b7e97 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e97
          have b7e123 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b7e13 X1 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X0 X2
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e141 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e153 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e123 X0 X1 x
               have i₂ := b7e13 X0 X0 x
               grind)
            | exact superpose b7e13 b7e123
            | (have j0 := b7e123 X0 X1 x
               grind)
            | exact resolve b7e123 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e123
          have b7e160 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e153 X0 X1
               have j1 := b7e141 X0 X1
               grind)
            | (have r₁ := b7e153 X0 X1
               have r₂ := b7e141 X0 X1
               grind)
            | (have r₁ := b7e153 X1 X0
               have r₂ := b7e141 X0 X1
               grind)
            | (have r₁ := b7e153 X1 X1
               have r₂ := b7e141 X1 X1
               grind)
            | exact resolve b7e153 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141 b7e153
          have b7e3405 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e96 (σ x)
               have i₂ := b7e74
               grind)
            | exact superpose b7e74 b7e96
            | (have j0 := b7e96 (σ x)
               grind)
            | (have r₁ := b7e96 (σ x)
               have r₂ := b7e74
               grind)
            | exact resolve b7e96 b7e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74 b7e96
          have b7e3406 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e3405
          have b7e3407 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e3406
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e3406
            | exact resolve b7e3406 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3406
          have b7e3408 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e3407
               have r₂ := b7e103
               grind)
            | exact resolve b7e3407 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103 b7e3407
          have b7e3409 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e3408
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e3408
            | exact resolve b7e3408 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3408
          have b7e3410 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e3409
               have i₂ := b7e85 x
               grind)
            | exact superpose b7e85 b7e3409
            | exact resolve b7e3409 b7e85
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85 b7e3409
          have b7e3415 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e3410
               grind)
            | exact superpose b7e3410 b7e14
            | exact resolve b7e14 b7e3410
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3410
          have b7e3430 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e3415
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e3415
            | exact resolve b7e3415 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3415
          have b7e3875 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e160 x y
               have i₂ := b7e3430
               grind)
            | exact superpose b7e3430 b7e160
            | (have j0 := b7e160 x y
               grind)
            | exact resolve b7e160 b7e3430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e160 b7e3430
          have b7e3879 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e3875
               have r₂ := b7e21
               grind)
            | exact resolve b7e3875 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e3875
          have b7e3885 : False := by grind
          exact b7e3885
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
            intro X0 X1 X2
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : (M.op x y) ≠ (M.op y y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e119 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X0 (M.op X2 (M.op X0 X0))) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e13 X1 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X0 X2
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
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
          have b8e138 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e149 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e119 X0 X1 x
               have i₂ := b8e13 X0 X0 x
               grind)
            | exact superpose b8e13 b8e119
            | (have j0 := b8e119 X0 X1 x
               grind)
            | exact resolve b8e119 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e153 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e149 X0 X1
               have j1 := b8e138 X0 X1
               grind)
            | (have r₁ := b8e149 X0 X1
               have r₂ := b8e138 X0 X1
               grind)
            | (have r₁ := b8e149 X1 X0
               have r₂ := b8e138 X0 X1
               grind)
            | (have r₁ := b8e149 X1 X1
               have r₂ := b8e138 X1 X1
               grind)
            | exact resolve b8e149 b8e138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138 b8e149
          have b8e6453 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e131 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e6454 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e6453
               have r₂ := b8e23
               grind)
            | exact resolve b8e6453 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6453
          have b8e6456 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e6454
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e6454
            | exact resolve b8e6454 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6454
          have b8e6462 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e6456
               grind)
            | exact superpose b8e6456 b8e20
            | exact resolve b8e20 b8e6456
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6456
          have b8e6610 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e6462
               have i₂ := b8e153 x y
               grind)
            | exact superpose b8e153 b8e6462
            | (have j1 := b8e153 x y
               grind)
            | exact resolve b8e6462 b8e153
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153 b8e6462
          have b8e6611 : (M.op x y) = (M.op y y) := by grind
          clear b8e6610
          have b8e6614 : False := by grind
          exact b8e6614

/-- `Equation3292`: `x ◇ x = y ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_pyy_pxx_pxy_Equation3292 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3292 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3292.models_iff G M).mp hM
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
      have b0e46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e46 (σ X0)
           grind)
        | exact superpose b0e46 b0e15
        | exact resolve b0e15 b0e46
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
      have b0e186 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e58 y
           grind)
        | exact superpose b0e58 b0e20
        | (have r₁ := b0e20
           have r₂ := b0e58 y
           grind)
        | exact resolve b0e20 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e58
      have b0e194 : False := by grind
      exact b0e194
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
      have b1e25 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X1 (M.op X2 X0)) X2 X3
           have i₂ := b1e10 X0 X2 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e26 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (M.op X1 X0) X2 X1
           have i₂ := b1e10 X0 X1 X2
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e40 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
      have b1e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e45 : (M.op x x) = (k x y) := by grind
      clear b1e40
      have b1e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e43 (σ X0)
           grind)
        | exact superpose b1e43 b1e15
        | exact resolve b1e15 b1e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e47 X0
           have i₂ := b1e43 X0
           grind)
        | exact superpose b1e43 b1e47
        | exact resolve b1e47 b1e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e43 b1e47
      have b1e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
      have b1e72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e67 X0 X1
           have i₂ := b1e52 X1
           grind)
        | exact superpose b1e52 b1e67
        | (have j0 := b1e67 X0 X1
           grind)
        | exact resolve b1e67 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e67
      have b1e196 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 X2 X1 (M.op X1 X2)
           have i₂ := b1e26 (M.op X1 X2) X0 X1
           grind)
        | exact superpose b1e26 b1e10
        | exact resolve b1e10 b1e26
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e1664 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 (σ X0))) (M.op X1 (M.op X2 (σ X0)))) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e25 (σ X0) X1 X2 X3
           have i₂ := b1e52 X0
           grind)
        | exact superpose b1e52 b1e25
        | exact resolve b1e25 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e25
      have b1e1867 : ∀ X0 X2 X3 : G, (M.op (σ X0) (σ X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
        intro X0 X2 X3
        first
        | (have i₁ := b1e1664 X0 x X2 X3
           have i₂ := b1e196 x X2 (σ X0)
           grind)
        | exact superpose b1e196 b1e1664
        | exact resolve b1e1664 b1e196
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e196 b1e1664
      have b1e1943 : ∀ X0 X2 X3 : G, (σ (M.op X0 X0)) = (M.op X2 (M.op X3 (σ (M.op X0 X0)))) := by
        intro X0 X2 X3
        first
        | (have i₁ := b1e1867 X0 X2 X3
           have i₂ := b1e52 X0
           grind)
        | exact superpose b1e52 b1e1867
        | exact resolve b1e1867 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1867
      have b1e2140 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e72 x y
           grind)
        | exact superpose b1e72 b1e18
        | (have j1 := b1e72 x y
           grind)
        | exact resolve b1e18 b1e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2160 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) (σ X0) X2
           have i₂ := b1e72 X0 X1
           grind)
        | exact superpose b1e72 b1e10
        | (have j1 := b1e72 X0 X1
           grind)
        | exact resolve b1e10 b1e72
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e72
      have b1e2183 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (M.op X2 (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e2160 X0 X1 X2
           have i₂ := b1e52 X1
           grind)
        | exact superpose b1e52 b1e2160
        | (have j0 := b1e2160 X0 X1 X2
           grind)
        | exact resolve b1e2160 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2160
      have b1e2184 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e2140
           have r₂ := b1e19
           grind)
        | exact resolve b1e2140 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2140
      have b1e2222 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e2184
           have i₂ := b1e45
           grind)
        | exact superpose b1e45 b1e2184
        | exact resolve b1e2184 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2184
      have b1e2241 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e2222
           have i₂ := b1e52 y
           grind)
        | exact superpose b1e52 b1e2222
        | exact resolve b1e2222 b1e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e52 b1e2222
      have b1e186141 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e2183 x y X0
           have i₂ := b1e45
           grind)
        | exact superpose b1e45 b1e2183
        | (have j0 := b1e2183 x y x
           grind)
        | exact resolve b1e2183 b1e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45 b1e2183
      have b1e186477 : ∀ X0 : G, (σ (M.op y y)) = (M.op (σ x) (M.op X0 (σ (M.op x x)))) := by
        intro X0
        first
        | (have j0 := b1e186141 X0
           grind)
        | (have r₁ := b1e186141 X0
           have r₂ := b1e19
           grind)
        | exact resolve b1e186141 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e186141
      have b1e186495 : (σ (M.op y y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e186477 x
           have i₂ := b1e1943 x (σ x) x
           grind)
        | exact superpose b1e1943 b1e186477
        | exact resolve b1e186477 b1e1943
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e1943 b1e186477
      have b1e186503 : False := by grind
      exact b1e186503
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
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
      have b2e41 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b2e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e41
      have b2e46 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e44
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e44
        | exact resolve b2e44 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e80 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e46
           grind)
        | exact superpose b2e46 b2e13
        | exact resolve b2e13 b2e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e82 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e80
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
           have i₂ := b2e43 x
           grind)
        | exact superpose b2e43 b2e83
        | exact resolve b2e83 b2e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e43 b2e83
      have b2e132 : (k x y) = (τ (σ (M.op x x))) := by
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
      have b2e133 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e132
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e132
        | exact resolve b2e132 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e132
      have b2e206 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e133
           grind)
        | exact superpose b2e133 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e133
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e133
      have b2e207 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b2e206
           have r₂ := b2e17
           grind)
        | exact resolve b2e206 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e206
      have b2e264 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e10 x x x
           have i₂ := b2e207
           grind)
        | exact superpose b2e207 b2e10
        | exact resolve b2e10 b2e207
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e207
      have b2e266 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e264 x
           have i₂ := b2e10 y x x
           grind)
        | exact superpose b2e10 b2e264
        | exact resolve b2e264 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e264
      have b2e269 : False := by grind
      exact b2e269
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
      have b3e40 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e40 (σ X0)
           grind)
        | exact superpose b3e40 b3e15
        | exact resolve b3e15 b3e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e43 X0
           have i₂ := b3e40 X0
           grind)
        | exact superpose b3e40 b3e43
        | exact resolve b3e43 b3e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e40 b3e43
      have b3e63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
      have b3e68 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e63 X0 X1
           have i₂ := b3e48 X1
           grind)
        | exact superpose b3e48 b3e63
        | (have j0 := b3e63 X0 X1
           grind)
        | exact resolve b3e63 b3e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e63
      have b3e2074 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e68 x y
           grind)
        | exact superpose b3e68 b3e16
        | (have j1 := b3e68 x y
           grind)
        | exact resolve b3e16 b3e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e68
      have b3e50773 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b3e2074
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2074
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2074 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2074
      have b3e50779 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b3e50773
      have b3e50780 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have r₁ := b3e50779
           have r₂ := b3e17
           grind)
        | exact resolve b3e50779 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e50779
      have b3e50785 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e50780
           grind)
        | exact superpose b3e50780 b3e18
        | exact resolve b3e18 b3e50780
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e50780
      have b3e50888 : False := by grind
      exact b3e50888

/-- `Equation3294`: `x ◇ x = y ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3294.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x y) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
    · have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op x y) := by grind
      have b0e20 : (σ x) = (M.op (σ x) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e21 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e18
        | exact resolve b0e18 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22 : (σ x) ≠ (σ x) := by
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
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op x y) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
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
        have b1e26 : x ≠ x ∨ y = (k x y) := by
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
        have b1e28 : y = (k x y) := by grind
        clear b1e26
        have b1e55 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e60 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e55
        have b1e61 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e23
             grind)
          | exact resolve b1e60 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e62 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e62
          | exact resolve b1e62 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e62
        have b1e64 : False := by grind
        exact b1e64
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op x y) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x ≠ x ∨ y = (k x y) := by
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
        have b2e25 : y = (k x y) := by grind
        clear b2e24
        have b2e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e769 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e71 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e34595 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e769 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e769
          | (have j0 := b2e769 x y
             grind)
          | exact resolve b2e769 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e769
        have b2e34608 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e34595
        have b2e34627 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e34608
             have r₂ := b2e22
             grind)
          | exact resolve b2e34608 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34608
        have b2e34635 : False := by grind
        exact b2e34635
  · rcases eq_or_ne (M.op x y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op x y) := by grind
        have b3e21 : y = (M.op x y) := by grind
        have b3e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
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
        have b3e24 : (σ (M.op x y)) ≠ (σ x) := by
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
        have b3e27 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e28 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e27
        have b3e29 : (σ y) = (σ (k x y)) := by
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
        have b3e46 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e49 : x = y ∨ x = (k x y) := by grind
        clear b3e46
        have b3e50 : x = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e23
             grind)
          | exact resolve b3e49 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e49
        have b3e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e29
          | exact resolve b3e29 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e50
        have b3e54 : False := by grind
        exact b3e54
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x y) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e27 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e28 : (σ y) ≠ (σ y) := by
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
        · have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op x y) := by grind
          have b5e22 : y = (M.op x y) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
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
          have b5e53 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e58 : x = y ∨ x = (k x y) := by grind
          clear b5e53
          have b5e59 : x = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e25
               grind)
            | exact resolve b5e58 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e776 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e30323 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e776 x y
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e776
            | (have j0 := b5e776 x y
               grind)
            | exact resolve b5e776 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e776
          have b5e30338 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e30323
          have b5e30345 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e30338
               have r₂ := b5e24
               grind)
            | exact resolve b5e30338 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30338
          have b5e30349 : False := by grind
          exact b5e30349
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op x y) := by grind
        have b6e21 : y ≠ (M.op x y) := by grind
        have b6e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e25 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e24
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
        have b6e31 : (k x y) = (τ (σ y)) := by
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
        have b6e32 : y = (k x y) := by
          first
          | (have i₁ := b6e31
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e31
          | exact resolve b6e31 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e61 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e63 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e61
        have b6e66 : x = (M.op x y) := by
          first
          | (have r₁ := b6e63
             have r₂ := b6e21
             grind)
          | exact resolve b6e63 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e69 : False := by grind
        exact b6e69
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op x y) := by grind
          have b7e22 : y ≠ (M.op x y) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ y)) := by grind
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
          have b7e49 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e49
          have b7e55 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e25
               grind)
            | exact resolve b7e54 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e54
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
          have b7e69 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e70 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e69
          have b7e72 : y = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e74 : False := by grind
          exact b7e74
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op x y) := by grind
          have b8e22 : y ≠ (M.op x y) := by grind
          have b8e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e338 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e383 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e338
               have r₂ := b8e24
               grind)
            | exact resolve b8e338 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338
          have b8e386 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e383
               have r₂ := b8e23
               grind)
            | exact resolve b8e383 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e383
          have b8e387 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e386
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e386
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e386 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e386
          have b8e388 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e387
          have b8e389 : x = (M.op x y) := by
            first
            | (have r₁ := b8e388
               have r₂ := b8e22
               grind)
            | exact resolve b8e388 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e388
          have b8e390 : False := by grind
          exact b8e390

/-- `Equation3294`: `x ◇ x = y ◇ (z ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3294 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3294 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3294.models_iff G M).mp hM
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
        have b1e55 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e60 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e55
        have b1e61 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e60
             have r₂ := b1e23
             grind)
          | exact resolve b1e60 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e62 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e61
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e61
          | exact resolve b1e61 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e61
        have b1e63 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e62
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e62
          | exact resolve b1e62 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e62
        have b1e64 : False := by grind
        exact b1e64
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
        have b2e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e576 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e73 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e27683 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e576 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e576
          | (have j0 := b2e576 x y
             grind)
          | exact resolve b2e576 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e576
        have b2e27690 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e27683
        have b2e27721 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e27690
             have r₂ := b2e22
             grind)
          | exact resolve b2e27690 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27690
        have b2e27735 : False := by grind
        exact b2e27735
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
        have b3e46 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e49 : x = y ∨ y = (k x y) := by grind
        clear b3e46
        have b3e50 : y = (k x y) := by
          first
          | (have r₁ := b3e49
             have r₂ := b3e23
             grind)
          | exact resolve b3e49 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e49
        have b3e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e29
          | exact resolve b3e29 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e50
        have b3e54 : False := by grind
        exact b3e54
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
          have b5e53 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          have b5e58 : x = y ∨ y = (k x y) := by grind
          clear b5e53
          have b5e59 : y = (k x y) := by
            first
            | (have r₁ := b5e58
               have r₂ := b5e25
               grind)
            | exact resolve b5e58 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e58
          have b5e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e589 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e62 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e32505 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e589 x y
               have i₂ := b5e59
               grind)
            | exact superpose b5e59 b5e589
            | (have j0 := b5e589 x y
               grind)
            | exact resolve b5e589 b5e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e59 b5e589
          have b5e32525 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e32505
          have b5e32542 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e32525
               have r₂ := b5e24
               grind)
            | exact resolve b5e32525 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32525
          have b5e32561 : False := by grind
          exact b5e32561
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
        have b6e61 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e63 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e61
        have b6e66 : y = (M.op x y) := by
          first
          | (have r₁ := b6e63
             have r₂ := b6e21
             grind)
          | exact resolve b6e63 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e69 : False := by grind
        exact b6e69
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
          have b7e49 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e54 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e49
          have b7e55 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e54
               have r₂ := b7e25
               grind)
            | exact resolve b7e54 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e54
          have b7e56 : (σ y) = (σ (k x y)) := by
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
          have b7e59 : (k x y) = (τ (σ y)) := by
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
          have b7e60 : y = (k x y) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e59
            | exact resolve b7e59 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e69 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
          have b7e70 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e69
          have b7e72 : x = (M.op x y) := by
            first
            | (have r₁ := b7e70
               have r₂ := b7e21
               grind)
            | exact resolve b7e70 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e74 : False := by grind
          exact b7e74
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
          have b8e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e323 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e54 x y
               grind)
            | exact superpose b8e54 b8e20
            | (have j1 := b8e54 x y
               grind)
            | exact resolve b8e20 b8e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e54
          have b8e363 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e323
               have r₂ := b8e24
               grind)
            | exact resolve b8e323 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e323
          have b8e366 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e363
               have r₂ := b8e23
               grind)
            | exact resolve b8e363 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e363
          have b8e367 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e366
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e366
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e366 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e366
          have b8e368 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e367
          have b8e369 : y = (M.op x y) := by
            first
            | (have r₁ := b8e368
               have r₂ := b8e22
               grind)
            | exact resolve b8e368 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e368
          have b8e370 : False := by grind
          exact b8e370

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pxy_pyy_pxx_pxy_Equation3296 :
    AutBox.GuardAut ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
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
      have b0e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e15 X0 X0
           have i₂ := b0e50 (σ X0)
           grind)
        | exact superpose b0e50 b0e15
        | exact resolve b0e15 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e59 X0
           have i₂ := b0e50 X0
           grind)
        | exact superpose b0e50 b0e59
        | exact resolve b0e59 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50 b0e59
      have b0e176 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e64 y
           grind)
        | exact superpose b0e64 b0e20
        | (have r₁ := b0e20
           have r₂ := b0e64 y
           grind)
        | exact resolve b0e20 b0e64
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20 b0e64
      have b0e184 : False := by grind
      exact b0e184
    · have b1e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
      have b1e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b1e10 (M.op X1 (M.op X1 X0)) X2 X3
           have i₂ := b1e10 X0 X3 X1
           grind)
        | exact superpose b1e10 b1e10
        | exact resolve b1e10 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e29 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
        intro X0 X2 X3
        first
        | (have i₁ := b1e26 X0 x X2 X3
           have i₂ := b1e10 X0 (M.op x (M.op x X0)) x
           grind)
        | (have i₁ := b1e26 X0 x X2 X3
           have i₂ := b1e10 (M.op x (M.op x X0)) x X2
           grind)
        | exact superpose b1e10 b1e26
        | exact resolve b1e26 b1e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e26
      have b1e42 : (M.op y y) ≠ (M.op y y) ∨ (M.op x x) = (k x y) := by
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
      have b1e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b1e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e49 : (M.op x x) = (k x y) := by grind
      clear b1e42
      have b1e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b1e15 X0 X0
           have i₂ := b1e47 (σ X0)
           grind)
        | exact superpose b1e47 b1e15
        | exact resolve b1e15 b1e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e58 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b1e53 X0
           have i₂ := b1e47 X0
           grind)
        | exact superpose b1e47 b1e53
        | exact resolve b1e53 b1e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47 b1e53
      have b1e75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
      have b1e80 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e75 X0 X1
           have i₂ := b1e58 X1
           grind)
        | exact superpose b1e58 b1e75
        | (have j0 := b1e75 X0 X1
           grind)
        | exact resolve b1e75 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e75
      have b1e228 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (σ (M.op X0 X0)))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e29 (σ X0) X2 x
           have i₂ := b1e58 X0
           grind)
        | exact superpose b1e58 b1e29
        | exact resolve b1e29 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e29
      have b1e2286 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e80 x y
           grind)
        | exact superpose b1e80 b1e18
        | (have j1 := b1e80 x y
           grind)
        | exact resolve b1e18 b1e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e2306 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X1)) = (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e10 (σ X1) X2 (σ X0)
           have i₂ := b1e80 X0 X1
           grind)
        | exact superpose b1e80 b1e10
        | (have j1 := b1e80 X0 X1
           grind)
        | exact resolve b1e10 b1e80
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e80
      have b1e2328 : ∀ X0 X1 X2 : G, (σ (M.op X1 X1)) = (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b1e2306 X0 X1 X2
           have i₂ := b1e58 X1
           grind)
        | exact superpose b1e58 b1e2306
        | (have j0 := b1e2306 X0 X1 X2
           grind)
        | exact resolve b1e2306 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2306
      have b1e2329 : (M.op (σ y) (σ y)) ≠ (σ (k x y)) := by
        first
        | (have r₁ := b1e2286
           have r₂ := b1e19
           grind)
        | exact resolve b1e2286 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2286
      have b1e2371 : (M.op (σ y) (σ y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e2329
           have i₂ := b1e49
           grind)
        | exact superpose b1e49 b1e2329
        | exact resolve b1e2329 b1e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e2329
      have b1e2394 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b1e2371
           have i₂ := b1e58 y
           grind)
        | exact superpose b1e58 b1e2371
        | exact resolve b1e2371 b1e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e58 b1e2371
      have b1e199177 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ x) (σ (M.op x x)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b1e2328 x y X0
           have i₂ := b1e49
           grind)
        | exact superpose b1e49 b1e2328
        | (have j0 := b1e2328 x y x
           grind)
        | exact resolve b1e2328 b1e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49 b1e2328
      have b1e199645 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (M.op (σ x) (σ (M.op x x)))) := by
        intro X0
        first
        | (have j0 := b1e199177 X0
           grind)
        | (have r₁ := b1e199177 X0
           have r₂ := b1e19
           grind)
        | exact resolve b1e199177 b1e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19 b1e199177
      have b1e199660 : (σ (M.op y y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b1e199645 x
           have i₂ := b1e228 x x (σ x)
           grind)
        | exact superpose b1e228 b1e199645
        | exact resolve b1e199645 b1e228
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e228 b1e199645
      have b1e199664 : False := by grind
      exact b1e199664
  · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1a | h1a
    · have b2e10 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
      have b2e44 : (M.op (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b2e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b2e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e48 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b2e44
      have b2e51 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b2e48
           have i₂ := b2e15 x y
           grind)
        | exact superpose b2e15 b2e48
        | exact resolve b2e48 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e88 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
        first
        | (have i₁ := b2e13 (σ x) (σ x)
           have i₂ := b2e51
           grind)
        | exact superpose b2e51 b2e13
        | exact resolve b2e13 b2e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e51
      have b2e90 : (σ (k x y)) = (k (σ x) (σ x)) := by grind
      clear b2e88
      have b2e91 : (σ (k x y)) = (σ (k x x)) := by
        first
        | (have i₁ := b2e90
           have i₂ := b2e15 x x
           grind)
        | exact superpose b2e15 b2e90
        | exact resolve b2e90 b2e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e90
      have b2e92 : (σ (k x y)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b2e91
           have i₂ := b2e47 x
           grind)
        | exact superpose b2e47 b2e91
        | exact resolve b2e91 b2e47
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e47 b2e91
      have b2e122 : (k x y) = (τ (σ (M.op x x))) := by
        first
        | (have i₁ := b2e11 (k x y)
           have i₂ := b2e92
           grind)
        | exact superpose b2e92 b2e11
        | exact resolve b2e11 b2e92
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e92
      have b2e123 : (k x y) = (M.op x x) := by
        first
        | (have i₁ := b2e122
           have i₂ := b2e11 (M.op x x)
           grind)
        | exact superpose b2e11 b2e122
        | exact resolve b2e122 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e122
      have b2e192 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e14 x y
           have i₂ := b2e123
           grind)
        | exact superpose b2e123 b2e14
        | (have j0 := b2e14 x y
           grind)
        | exact resolve b2e14 b2e123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e123
      have b2e193 : (M.op x y) = (M.op x x) := by
        first
        | (have r₁ := b2e192
           have r₂ := b2e17
           grind)
        | exact resolve b2e192 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e192
      have b2e241 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x (M.op x y))) := by
        intro X0
        first
        | (have i₁ := b2e10 x x x
           have i₂ := b2e193
           grind)
        | exact superpose b2e193 b2e10
        | exact resolve b2e10 b2e193
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e193
      have b2e243 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b2e241 x
           have i₂ := b2e10 y x x
           grind)
        | (have i₁ := b2e241 (M.op x (M.op x y))
           have i₂ := b2e10 (M.op x (M.op x y)) x x
           grind)
        | exact superpose b2e10 b2e241
        | exact resolve b2e241 b2e10
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e241
      have b2e246 : False := by grind
      exact b2e246
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
      have b3e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b3e13 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 X0
           have i₂ := b3e44 (σ X0)
           grind)
        | exact superpose b3e44 b3e15
        | exact resolve b3e15 b3e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b3e49 X0
           have i₂ := b3e44 X0
           grind)
        | exact superpose b3e44 b3e49
        | exact resolve b3e49 b3e44
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e44 b3e49
      have b3e71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
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
      have b3e76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e71 X0 X1
           have i₂ := b3e54 X1
           grind)
        | exact superpose b3e54 b3e71
        | (have j0 := b3e71 X0 X1
           grind)
        | exact resolve b3e71 b3e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e71
      have b3e2107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b3e16
           have i₂ := b3e76 x y
           grind)
        | exact superpose b3e76 b3e16
        | (have j1 := b3e76 x y
           grind)
        | exact resolve b3e16 b3e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e76
      have b3e66595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b3e2107
           have i₂ := b3e14 x y
           grind)
        | exact superpose b3e14 b3e2107
        | (have j1 := b3e14 x y
           grind)
        | exact resolve b3e2107 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e2107
      have b3e66601 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
      clear b3e66595
      have b3e66602 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have r₁ := b3e66601
           have r₂ := b3e17
           grind)
        | exact resolve b3e66601 b3e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e66601
      have b3e66607 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e66602
           grind)
        | exact superpose b3e66602 b3e18
        | exact resolve b3e18 b3e66602
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e66602
      have b3e66740 : False := by grind
      exact b3e66740
