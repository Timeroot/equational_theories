import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
           have i₂ := b0e43 (σ X0)
           grind)
        | exact superpose b0e43 b0e17
        | exact resolve b0e17 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e56 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e53 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e53
        | exact resolve b0e53 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e53
      have b0e173 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
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
      have b0e184 : False := by grind
      exact b0e184
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
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
        have b1e27 : (M.op y y) = (M.op (M.op x (M.op x x)) x) := by
          first
          | (have i₁ := b1e12 y x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e30 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b1e27
             have i₂ := b1e12 x x
             grind)
          | exact superpose b1e12 b1e27
          | exact resolve b1e27 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e49 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        have b1e55 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e49
        have b1e59 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e55
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e55
          | exact resolve b1e55 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e60 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e59
             have i₂ := b1e52 y
             grind)
          | exact superpose b1e52 b1e59
          | exact resolve b1e59 b1e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e52 b1e59
        have b1e61 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e60
             have i₂ := b1e30
             grind)
          | exact superpose b1e30 b1e60
          | exact resolve b1e60 b1e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e30 b1e60
        have b1e62 : False := by grind
        exact b1e62
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
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
        have b2e27 : (M.op y y) = (M.op (M.op x (M.op x x)) x) := by
          first
          | (have i₁ := b2e12 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b2e27
             have i₂ := b2e12 x x
             grind)
          | exact superpose b2e12 b2e27
          | exact resolve b2e27 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e47 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b2e51 : (M.op y y) = (k x y) := by grind
        clear b2e47
        have b2e54 : (M.op x x) = (k x y) := by
          first
          | (have i₁ := b2e51
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e51
          | exact resolve b2e51 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e51
        have b2e93 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e3073 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e93 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e3074 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e3073
             have r₂ := b2e21
             grind)
          | exact resolve b2e3073 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3073
        have b2e3079 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e3074
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e3074
          | exact resolve b2e3074 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3074
        have b2e3083 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e3079
             have i₂ := b2e54
             grind)
          | exact superpose b2e54 b2e3079
          | exact resolve b2e3079 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e3079
        have b2e3085 : False := by grind
        exact b2e3085
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
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
        have b3e42 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) := by
          first
          | (have i₁ := b3e12 (σ y) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e12
          | exact resolve b3e12 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b3e42
             have i₂ := b3e12 (σ x) (σ x)
             grind)
          | exact superpose b3e12 b3e42
          | exact resolve b3e42 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e55 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e59 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e55
        have b3e62 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e59
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e59
          | exact resolve b3e59 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e83 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e62
             grind)
          | exact superpose b3e62 b3e15
          | exact resolve b3e15 b3e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e85 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e83
        have b3e86 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e85
          | exact resolve b3e85 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e87 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e57 y
             grind)
          | exact superpose b3e57 b3e86
          | exact resolve b3e86 b3e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57 b3e86
        have b3e88 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e87
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e87
          | exact resolve b3e87 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e87
        have b3e156 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e62
             have i₂ := b3e43
             grind)
          | exact superpose b3e43 b3e62
          | exact resolve b3e62 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43 b3e62
        have b3e169 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e156
             have i₂ := b3e88
             grind)
          | exact superpose b3e88 b3e156
          | exact resolve b3e156 b3e88
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e88 b3e156
        have b3e173 : False := by grind
        exact b3e173
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
          have b4e68 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e72 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e68
          have b4e75 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e72
            | exact resolve b4e72 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e76 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e75
               have i₂ := b4e70 y
               grind)
            | exact superpose b4e70 b4e75
            | exact resolve b4e75 b4e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70 b4e75
          have b4e77 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e76
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e76
            | exact resolve b4e76 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e78 : False := by grind
          exact b4e78
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
          have b5e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
               have i₂ := b5e67 (σ X0)
               grind)
            | exact superpose b5e67 b5e19
            | exact resolve b5e19 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e81 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e72 X0
               have i₂ := b5e67 X0
               grind)
            | exact superpose b5e67 b5e72
            | exact resolve b5e72 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67 b5e72
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
          have b5e132 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e1056 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e90 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e90
          have b5e1058 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e1056
               have r₂ := b5e21
               grind)
            | exact resolve b5e1056 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1056
          have b5e3806 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e132 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e132
          have b5e3807 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e3806
               have r₂ := b5e23
               grind)
            | exact resolve b5e3806 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3806
          have b5e3812 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e3807
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e3807
            | exact resolve b5e3807 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3807
          have b5e3816 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e3812
               have i₂ := b5e1058
               grind)
            | exact superpose b5e1058 b5e3812
            | exact resolve b5e3812 b5e1058
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1058 b5e3812
          have b5e3820 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e3816
               grind)
            | exact superpose b5e3816 b5e23
            | exact resolve b5e23 b5e3816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e3816
          have b5e3863 : False := by grind
          exact b5e3863
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
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
        have b6e41 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ x))) (σ x)) := by
          first
          | (have i₁ := b6e12 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e12 (σ x) (σ x)
             grind)
          | exact superpose b6e12 b6e41
          | exact resolve b6e41 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e55 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e53
        have b6e57 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e55
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e55
          | exact resolve b6e55 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55
        have b6e77 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e57
             grind)
          | exact superpose b6e57 b6e15
          | exact resolve b6e15 b6e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e79 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e77
        have b6e80 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e79
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e79
          | exact resolve b6e79 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e79
        have b6e81 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e80
             have i₂ := b6e54 y
             grind)
          | exact superpose b6e54 b6e80
          | exact resolve b6e80 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54 b6e80
        have b6e134 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e81
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e81
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e81 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e143 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have r₁ := b6e134
             have r₂ := b6e20
             grind)
          | exact resolve b6e134 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e144 : (σ (M.op x y)) = (σ (M.op y y)) := by
          first
          | (have r₁ := b6e143
             have r₂ := b6e21
             grind)
          | exact resolve b6e143 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e148 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e57
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e57
          | exact resolve b6e57 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e57
        have b6e161 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e148
             have i₂ := b6e81
             grind)
          | exact superpose b6e81 b6e148
          | exact resolve b6e148 b6e81
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e81 b6e148
        have b6e165 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e161
             have i₂ := b6e144
             grind)
          | exact superpose b6e144 b6e161
          | exact resolve b6e161 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144 b6e161
        have b6e168 : False := by grind
        exact b6e168
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
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
          have b7e66 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e66
          have b7e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e68
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e68
            | exact resolve b7e68 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68
          have b7e71 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e70
               have i₂ := b7e67 y
               grind)
            | exact superpose b7e67 b7e70
            | exact resolve b7e70 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e70
          have b7e73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e67 (σ X0)
               grind)
            | exact superpose b7e67 b7e19
            | exact resolve b7e19 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e73 X0
               have i₂ := b7e67 X0
               grind)
            | exact superpose b7e67 b7e73
            | exact resolve b7e73 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e73
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
          have b7e94 : ∀ X0 : G, (M.op X0 (σ y)) ≠ (σ (M.op y y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e95 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e71
               grind)
            | exact superpose b7e71 b7e23
            | exact resolve b7e23 b7e71
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e101 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e95
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e95
            | exact resolve b7e95 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e95
          have b7e120 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 X0
               have i₂ := b7e18 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X0
               have i₂ := b7e18 X0 X1
               grind)
            | exact superpose b7e18 b7e13
            | (have j1 := b7e18 X0 X1
               grind)
            | exact resolve b7e13 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e147 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e120 X0 X1
               have i₂ := b7e13 X0 X0
               grind)
            | exact superpose b7e13 b7e120
            | (have j0 := b7e120 X0 X1
               grind)
            | exact resolve b7e120 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e120
          have b7e154 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e147 X0 X1
               have j1 := b7e135 X0 X1
               grind)
            | (have r₁ := b7e147 X0 X1
               have r₂ := b7e135 X0 X1
               grind)
            | (have r₁ := b7e147 X1 X0
               have r₂ := b7e135 X0 X1
               grind)
            | (have r₁ := b7e147 X1 X1
               have r₂ := b7e135 X1 X1
               grind)
            | exact resolve b7e147 b7e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e135 b7e147
          have b7e1710 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e1721 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e1710
          have b7e1724 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e1721
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e1721
            | exact resolve b7e1721 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1721
          have b7e1727 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e1724
               have r₂ := b7e101
               grind)
            | exact resolve b7e1724 b7e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e101 b7e1724
          have b7e1729 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1727
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e1727
            | exact resolve b7e1727 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1727
          have b7e1730 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e1729
               have i₂ := b7e82 x
               grind)
            | exact superpose b7e82 b7e1729
            | exact resolve b7e1729 b7e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82 b7e1729
          have b7e1735 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e1730
               grind)
            | exact superpose b7e1730 b7e14
            | exact resolve b7e14 b7e1730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1730
          have b7e1752 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e1735
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e1735
            | exact resolve b7e1735 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1735
          have b7e2027 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e154 x y
               have i₂ := b7e1752
               grind)
            | exact superpose b7e1752 b7e154
            | (have j0 := b7e154 x y
               grind)
            | exact resolve b7e154 b7e1752
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e154 b7e1752
          have b7e2031 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e2027
               have r₂ := b7e21
               grind)
            | exact resolve b7e2027 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e2027
          have b7e2037 : False := by grind
          exact b7e2037
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
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
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e116 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e13 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X0 X1
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e125 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e143 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e116 X0 X1
               have i₂ := b8e13 X0 X0
               grind)
            | exact superpose b8e13 b8e116
            | (have j0 := b8e116 X0 X1
               grind)
            | exact resolve b8e116 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e147 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               have j1 := b8e132 X0 X1
               grind)
            | (have r₁ := b8e143 X0 X1
               have r₂ := b8e132 X0 X1
               grind)
            | (have r₁ := b8e143 X1 X0
               have r₂ := b8e132 X0 X1
               grind)
            | (have r₁ := b8e143 X1 X1
               have r₂ := b8e132 X1 X1
               grind)
            | exact resolve b8e143 b8e132
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132 b8e143
          have b8e3360 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e125 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e125
          have b8e3361 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e3360
               have r₂ := b8e23
               grind)
            | exact resolve b8e3360 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3360
          have b8e3366 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e3361
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e3361
            | exact resolve b8e3361 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3361
          have b8e3375 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3366
               grind)
            | exact superpose b8e3366 b8e20
            | exact resolve b8e20 b8e3366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3366
          have b8e3490 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e3375
               have i₂ := b8e147 x y
               grind)
            | exact superpose b8e147 b8e3375
            | (have j1 := b8e147 x y
               grind)
            | exact resolve b8e3375 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147 b8e3375
          have b8e3491 : (M.op x y) = (M.op y y) := by grind
          clear b8e3490
          have b8e3494 : False := by grind
          exact b8e3494

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
      have b0e30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
      have b0e45 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e54 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
        intro X0
        first
        | (have i₁ := b0e22 X0 (τ X0)
           have i₂ := b0e45 (τ X0)
           grind)
        | exact superpose b0e45 b0e22
        | exact resolve b0e22 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e54 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e54
        | exact resolve b0e54 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e52
        | exact resolve b0e52 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e52
      have b0e59 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e55 X0
           have i₂ := b0e45 X0
           grind)
        | exact superpose b0e45 b0e55
        | exact resolve b0e55 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e80 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 X0
           have i₂ := b0e16 X1 X0
           grind)
        | (have i₁ := b0e11 X1 X1
           have i₂ := b0e16 X0 X1
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X1 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e16 X1 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e100 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e80 X0 X1
           have i₂ := b0e11 X0 X0
           grind)
        | exact superpose b0e11 b0e80
        | (have j0 := b0e80 X0 X1
           grind)
        | exact resolve b0e80 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e105 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e100 X0 X1
           have j1 := b0e91 X0 X1
           grind)
        | (have r₁ := b0e100 X0 X1
           have r₂ := b0e91 X0 X1
           grind)
        | (have r₁ := b0e100 X1 X0
           have r₂ := b0e91 X0 X1
           grind)
        | (have r₁ := b0e100 X1 X1
           have r₂ := b0e91 X1 X1
           grind)
        | exact resolve b0e100 b0e91
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91 b0e100
      have b0e214 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e105 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e105 X0 X1
           grind)
        | exact superpose b0e105 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e105 X1 X0
           grind)
        | (have r₁ := b0e14 X1 X0
           have r₂ := b0e105 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e105 X1 X1
           grind)
        | exact resolve b0e14 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e217 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 X1
           have i₂ := b0e105 (τ X0) X1
           grind)
        | exact superpose b0e105 b0e22
        | (have j1 := b0e105 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e218 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e17 X1 X0
           have i₂ := b0e105 (σ X0) (σ X1)
           grind)
        | exact superpose b0e105 b0e17
        | (have j1 := b0e105 (σ X0) (σ X1)
           grind)
        | exact resolve b0e17 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e222 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        first
        | (have j0 := b0e214 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e214
      have b0e225 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e218 X0 X1
           have i₂ := b0e57 X1
           grind)
        | exact superpose b0e57 b0e218
        | (have j0 := b0e218 X0 X1
           grind)
        | exact resolve b0e218 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e218
      have b0e2149 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e30 X1 X0
           have i₂ := b0e222 X1 (σ X0)
           grind)
        | exact superpose b0e222 b0e30
        | (have j1 := b0e222 X1 (σ X0)
           grind)
        | exact resolve b0e30 b0e222
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e2153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e21 X1 X0
           have i₂ := b0e222 (τ X1) X0
           grind)
        | exact superpose b0e222 b0e21
        | (have j1 := b0e222 (τ X1) X0
           grind)
        | exact resolve b0e21 b0e222
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21 b0e222
      have b0e2234 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (σ (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e2149 X0 X1
           have i₂ := b0e57 X0
           grind)
        | exact superpose b0e57 b0e2149
        | (have j0 := b0e2149 X0 X1
           grind)
        | exact resolve b0e2149 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2149
      have b0e2243 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e2234 X0 X1
           have i₂ := b0e12 (M.op X0 X0)
           grind)
        | exact superpose b0e12 b0e2234
        | (have j0 := b0e2234 X0 X1
           grind)
        | exact resolve b0e2234 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2234
      have b0e10473 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e217 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e217
        | exact resolve b0e217 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e217
      have b0e10720 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e10473 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e10473
        | (have j0 := b0e10473 X0 X1
           grind)
        | exact resolve b0e10473 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10473
      have b0e16242 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (σ X1) (σ X0)
           have i₂ := b0e225 X0 X1
           grind)
        | exact superpose b0e225 b0e15
        | (have j0 := b0e15 (σ X0) (σ X1)
           have j1 := b0e225 X1 X0
           grind)
        | exact resolve b0e15 b0e225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e16300 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e225 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e225
      have b0e16320 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e16242 X0 X1
           have i₂ := b0e57 X1
           grind)
        | exact superpose b0e57 b0e16242
        | (have j0 := b0e16242 X0 X1
           grind)
        | exact resolve b0e16242 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16242
      have b0e16418 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e16320 X0 X1
           have i₂ := b0e57 X0
           grind)
        | exact superpose b0e57 b0e16320
        | (have j0 := b0e16320 X0 X1
           grind)
        | exact resolve b0e16320 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16320
      have b0e16470 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e16418 X0 X1
           have j1 := b0e16300 X1 X0
           grind)
        | (have r₁ := b0e16418 X1 X0
           have r₂ := b0e16300 X0 X1
           grind)
        | exact resolve b0e16418 b0e16300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16418
      have b0e16494 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e16470 X0 X1
           have i₂ := b0e57 X0
           grind)
        | exact superpose b0e57 b0e16470
        | (have j0 := b0e16470 X0 X1
           grind)
        | exact resolve b0e16470 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16470
      have b0e16503 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e16494 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e16494
        | (have j0 := b0e16494 X0 X1
           grind)
        | exact resolve b0e16494 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16494
      have b0e16505 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e16503 X0 X1
           have j1 := b0e16300 X1 X0
           grind)
        | (have r₁ := b0e16503 X1 X0
           have r₂ := b0e16300 X0 X1
           grind)
        | exact resolve b0e16503 b0e16300
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16300 b0e16503
      have b0e21860 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 X0 X1
           have i₂ := b0e10720 X1 X0
           grind)
        | (have i₁ := b0e14 X1 X1
           have i₂ := b0e10720 X0 X1
           grind)
        | exact superpose b0e10720 b0e14
        | (have j0 := b0e14 X0 X0
           have j1 := b0e10720 X1 X0
           grind)
        | (have r₁ := b0e14 X1 X0
           have r₂ := b0e10720 X0 X1
           grind)
        | (have r₁ := b0e14 X1 X1
           have r₂ := b0e10720 X1 X1
           grind)
        | exact resolve b0e14 b0e10720
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10720
      have b0e21936 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
        intro X0 X1
        first
        | (have j0 := b0e21860 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21860
      have b0e31446 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e2243 X1 (σ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e2243
        | (have j0 := b0e2243 X1 (σ X0)
           grind)
        | exact resolve b0e2243 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2243
      have b0e31790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e31446 X0 X1
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e31446
        | (have j0 := b0e31446 X0 X1
           grind)
        | exact resolve b0e31446 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31446
      have b0e58749 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e31790 y x
           grind)
        | exact superpose b0e31790 b0e18
        | (have j1 := b0e31790 y x
           grind)
        | exact resolve b0e18 b0e31790
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31790
      have b0e59461 : (M.op x x) = (k y x) := by
        first
        | (have j1 := b0e21936 y x
           grind)
        | (have r₁ := b0e58749
           have r₂ := b0e21936 y x
           grind)
        | exact resolve b0e58749 b0e21936
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21936 b0e58749
      have b0e59987 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e105 x y
           have i₂ := b0e59461
           grind)
        | exact superpose b0e59461 b0e105
        | (have j0 := b0e105 x y
           grind)
        | exact resolve b0e105 b0e59461
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e191515 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X1))) = (k (σ (τ X1)) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e22 X0 (τ X1)
           have i₂ := b0e2153 (τ X0) X1
           grind)
        | exact superpose b0e2153 b0e22
        | (have j1 := b0e2153 (τ X0) X1
           grind)
        | exact resolve b0e22 b0e2153
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e2153
      have b0e191535 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X1 (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e191515 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e191515
        | (have j0 := b0e191515 X0 X1
           grind)
        | exact resolve b0e191515 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191515
      have b0e191727 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e191535 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e191535
        | (have j0 := b0e191535 X0 X1
           grind)
        | exact resolve b0e191535 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191535
      have b0e191794 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b0e191727 X0 X1
           have i₂ := b0e59 X0
           grind)
        | exact superpose b0e59 b0e191727
        | (have j0 := b0e191727 X0 X1
           grind)
        | exact resolve b0e191727 b0e59
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59 b0e191727
      have b0e193703 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) (τ (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e191794 (σ X1) (σ X0)
           have i₂ := b0e17 X0 X1
           grind)
        | exact superpose b0e17 b0e191794
        | exact resolve b0e191794 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e191794
      have b0e195077 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) (τ (σ X0)))) := by
        intro X0 X1
        first
        | (have i₁ := b0e193703 X0 X1
           have i₂ := b0e57 X1
           grind)
        | exact superpose b0e57 b0e193703
        | (have j0 := b0e193703 X0 X1
           grind)
        | exact resolve b0e193703 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e57 b0e193703
      have b0e195210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e195077 X0 X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e195077
        | (have j0 := b0e195077 X0 X1
           grind)
        | exact resolve b0e195077 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195077
      have b0e195257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e195210 X0 X1
           have i₂ := b0e12 X1
           grind)
        | exact superpose b0e12 b0e195210
        | (have j0 := b0e195210 X0 X1
           grind)
        | exact resolve b0e195210 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195210
      have b0e228603 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e195257 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e195257
      have b0e254324 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e228603 y y
           have i₂ := b0e59987
           grind)
        | exact superpose b0e59987 b0e228603
        | exact resolve b0e228603 b0e59987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59987 b0e228603
      have b0e254335 : (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
      clear b0e254324
      have b0e254344 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e254335
           have i₂ := b0e45 y
           grind)
        | exact superpose b0e45 b0e254335
        | exact resolve b0e254335 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e254335
      have b0e297253 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e16505 y x
           have i₂ := b0e59461
           grind)
        | exact superpose b0e59461 b0e16505
        | (have j0 := b0e16505 y x
           grind)
        | exact resolve b0e16505 b0e59461
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e16505
      have b0e297277 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
      clear b0e297253
      have b0e299570 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e297277
           grind)
        | exact superpose b0e297277 b0e18
        | exact resolve b0e18 b0e297277
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e297277
      have b0e299985 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
        first
        | (have i₁ := b0e299570
           have i₂ := b0e254344
           grind)
        | exact superpose b0e254344 b0e299570
        | (have r₁ := b0e299570
           have r₂ := b0e254344
           grind)
        | exact resolve b0e299570 b0e254344
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e254344
      have b0e299987 : (M.op x y) = (M.op x x) := by grind
      clear b0e299985
      have b0e302122 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e299987
           grind)
        | exact superpose b0e299987 b0e15
        | (have j0 := b0e15 x x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e299987
           grind)
        | exact resolve b0e15 b0e299987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e302205 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
      clear b0e302122
      have b0e302258 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
        first
        | (have i₁ := b0e302205
           have i₂ := b0e59461
           grind)
        | exact superpose b0e59461 b0e302205
        | exact resolve b0e302205 b0e59461
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e59461 b0e302205
      have b0e302259 : (M.op x x) = (M.op y y) := by grind
      clear b0e302258
      have b0e303700 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e299570
           have i₂ := b0e302259
           grind)
        | exact superpose b0e302259 b0e299570
        | exact resolve b0e299570 b0e302259
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e299570 b0e302259
      have b0e303892 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e303700
           have i₂ := b0e299987
           grind)
        | exact superpose b0e299987 b0e303700
        | exact resolve b0e303700 b0e299987
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e299987 b0e303700
      have b0e303893 : False := by grind
      exact b0e303893
    · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
          grind
        have b1e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e41 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (M.op (σ y) (σ x))) (σ y)) := by
          first
          | (have i₁ := b1e12 (σ y) (σ y)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e12 (σ x) (σ y)
             grind)
          | exact superpose b1e12 b1e41
          | exact resolve b1e41 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : False := by grind
        exact b1e43
      · have b2e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y x) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (M.op (σ y) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
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
        have b2e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e55 : (k x y) = (M.op y y) := by grind
        clear b2e50
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
        have b2e73 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X1) ∨ (M.op X2 X1) = (M.op X2 X2) ∨ (M.op X2 X1) = (k X1 X2) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e17 X1 X2
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e17 X0 X1
             have i₂ := b2e17 X0 X0
             grind)
          | exact superpose b2e17 b2e17
          | (have j0 := b2e17 X1 X2
             have j1 := b2e17 X1 X2
             grind)
          | exact resolve b2e17 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e90 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X1 X0
             have i₂ := b2e17 X1 X0
             grind)
          | (have i₁ := b2e12 X1 X1
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e12
          | (have j1 := b2e17 X1 X0
             grind)
          | exact resolve b2e12 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e17 X1 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e90 X0 X1
             have i₂ := b2e12 X0 X0
             grind)
          | exact superpose b2e12 b2e90
          | (have j0 := b2e90 X0 X1
             grind)
          | exact resolve b2e90 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e90
        have b2e118 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e113 X0 X1
             have j1 := b2e103 X0 X1
             grind)
          | (have r₁ := b2e113 X0 X1
             have r₂ := b2e103 X0 X1
             grind)
          | (have r₁ := b2e113 X1 X0
             have r₂ := b2e103 X0 X1
             grind)
          | (have r₁ := b2e113 X1 X1
             have r₂ := b2e103 X1 X1
             grind)
          | exact resolve b2e113 b2e103
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e103 b2e113
        have b2e146 : (M.op (σ y) (σ x)) ≠ (σ (M.op y y)) := by
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
        have b2e234 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e118 X1 X0
             grind)
          | (have i₁ := b2e15 X1 X1
             have i₂ := b2e118 X0 X1
             grind)
          | exact superpose b2e118 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e118 X1 X0
             grind)
          | (have r₁ := b2e15 X1 X0
             have r₂ := b2e118 X0 X1
             grind)
          | (have r₁ := b2e15 X1 X1
             have r₂ := b2e118 X1 X1
             grind)
          | exact resolve b2e15 b2e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e242 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e234 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e234
        have b2e2055 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          first
          | (have j0 := b2e242 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e242
        have b2e5276 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e73 (σ y) (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e73 X0 (σ x) (σ y)
             grind)
          | exact superpose b2e73 b2e21
          | (have j1 := b2e73 (σ y) (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e73 (σ x) (σ x) (σ y)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e73 (σ y) (σ x) (σ x)
             grind)
          | exact resolve b2e21 b2e73
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e5647 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ x)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5276 X0
             have j1 := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5276 X0
             have r₂ := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5276 (σ x)
             have r₂ := b2e2055 (σ x) (σ x)
             grind)
          | (have r₁ := b2e5276 x
             have r₂ := b2e2055 (σ x) x
             grind)
          | exact resolve b2e5276 b2e2055
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5276
        have b2e5872 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op X0 (σ x)) ∨ (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5647 X0
             have j1 := b2e2055 (σ x) (σ y)
             grind)
          | (have r₁ := b2e5647 (σ x)
             have r₂ := b2e2055 (σ x) (σ x)
             grind)
          | (have r₁ := b2e5647 x
             have r₂ := b2e2055 (σ x) x
             grind)
          | exact resolve b2e5647 b2e2055
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2055 b2e5647
        have b2e6040 : ∀ X0 : G, (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e5872 (σ y)
             have j1 := b2e118 (σ y) (σ x)
             grind)
          | (have r₁ := b2e5872 X0
             have r₂ := b2e118 X0 (σ x)
             grind)
          | (have r₁ := b2e5872 (σ x)
             have r₂ := b2e118 (σ x) (σ x)
             grind)
          | exact resolve b2e5872 b2e118
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e118 b2e5872
        have b2e6098 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (k x y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e6040 X0
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e6040
          | (have j0 := b2e6040 X0
             grind)
          | exact resolve b2e6040 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6040
        have b2e6106 : ∀ X0 : G, (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e6098 X0
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e6098
          | (have j0 := b2e6098 X0
             grind)
          | exact resolve b2e6098 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6098
        have b2e6112 : ∀ X0 : G, (M.op X0 (σ x)) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e6106 X0
             grind)
          | (have r₁ := b2e6106 X0
             have r₂ := b2e146
             grind)
          | exact resolve b2e6106 b2e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6106
        have b2e6122 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e18 x X0
             have i₂ := b2e6112 (σ X0)
             grind)
          | exact superpose b2e6112 b2e18
          | exact resolve b2e18 b2e6112
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e6112
        have b2e6887 : (σ (M.op y y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b2e146
             have i₂ := b2e6122 y
             grind)
          | exact superpose b2e6122 b2e146
          | exact resolve b2e146 b2e6122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e146 b2e6122
        have b2e6991 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e6887
             have i₂ := b2e55
             grind)
          | exact superpose b2e55 b2e6887
          | exact resolve b2e6887 b2e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55 b2e6887
        have b2e6992 : False := by grind
        exact b2e6992
  · rcases eq_or_ne (M.op y x) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b3e21 : (M.op y x) = (M.op y y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e30 : (M.op y x) = (M.op (M.op y (M.op y x)) y) := by
          first
          | (have i₁ := b3e12 y y
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : (M.op x x) = (M.op y x) := by
          first
          | (have i₁ := b3e30
             have i₂ := b3e12 x y
             grind)
          | exact superpose b3e12 b3e30
          | exact resolve b3e30 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30
        have b3e34 : False := by grind
        exact b3e34
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
            grind
          have b4e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b4e22 : (M.op y x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : (M.op y x) = (M.op (M.op y (M.op y x)) y) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e13 x y
               grind)
            | exact superpose b4e13 b4e32
            | exact resolve b4e32 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e36 : False := by grind
          exact b4e36
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x x) ≠ (M.op y x) := by grind
          have b5e22 : (M.op y x) = (M.op y y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : (M.op y x) = (M.op (M.op y (M.op y x)) y) := by
            first
            | (have i₁ := b5e13 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e13 x y
               grind)
            | exact superpose b5e13 b5e32
            | exact resolve b5e32 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e36 : False := by grind
          exact b5e36
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y x) := by grind
        have b6e21 : (M.op y x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e54 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e52
        have b6e56 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e75 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e56
             grind)
          | exact superpose b6e56 b6e15
          | exact resolve b6e15 b6e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e56
        have b6e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e75
        have b6e78 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e77
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e77
          | exact resolve b6e77 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e77
        have b6e79 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e78
             have i₂ := b6e53 y
             grind)
          | exact superpose b6e53 b6e78
          | exact resolve b6e78 b6e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53 b6e78
        have b6e134 : (k x y) = (τ (σ (M.op y y))) := by
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
        have b6e135 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e134
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e134
          | exact resolve b6e134 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e134
        have b6e182 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) ∨ (M.op y x) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e135
             grind)
          | exact superpose b6e135 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e135
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e135
        have b6e183 : (M.op y x) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by grind
        clear b6e182
        have b6e185 : (M.op x x) = (M.op y x) := by
          first
          | (have r₁ := b6e183
             have r₂ := b6e21
             grind)
          | exact resolve b6e183 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e183
        have b6e187 : False := by grind
        exact b6e187
      · rcases eq_or_ne (M.op (σ y) (σ x)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
            grind
          have b7e23 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e50 : (M.op (σ y) (σ x)) = (M.op (M.op (σ y) (M.op (σ y) (σ x))) (σ y)) := by
            first
            | (have i₁ := b7e13 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e51 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e13 (σ x) (σ y)
               grind)
            | exact superpose b7e13 b7e50
            | exact resolve b7e50 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e52 : False := by grind
          exact b7e52
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
          have b8e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e65 (σ X0)
               grind)
            | exact superpose b8e65 b8e19
            | exact resolve b8e19 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
            intro X0
            first
            | (have i₁ := b8e26 X0 (τ X0)
               have i₂ := b8e65 (τ X0)
               grind)
            | exact superpose b8e65 b8e26
            | exact resolve b8e26 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e74 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e71 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e71
            | exact resolve b8e71 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e71
          have b8e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e68 X0
               have i₂ := b8e65 X0
               grind)
            | exact superpose b8e65 b8e68
            | exact resolve b8e68 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e68
          have b8e80 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have i₁ := b8e74 X0
               have i₂ := b8e65 X0
               grind)
            | exact superpose b8e65 b8e74
            | exact resolve b8e74 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e119 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 X0
               have i₂ := b8e18 X1 X0
               grind)
            | (have i₁ := b8e13 X1 X1
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e13
            | (have j1 := b8e18 X1 X0
               grind)
            | exact resolve b8e13 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e18 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e142 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e119 X0 X1
               have i₂ := b8e13 X0 X0
               grind)
            | exact superpose b8e13 b8e119
            | (have j0 := b8e119 X0 X1
               grind)
            | exact resolve b8e119 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e119
          have b8e147 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e142 X0 X1
               have j1 := b8e133 X0 X1
               grind)
            | (have r₁ := b8e142 X0 X1
               have r₂ := b8e133 X0 X1
               grind)
            | (have r₁ := b8e142 X1 X0
               have r₂ := b8e133 X0 X1
               grind)
            | (have r₁ := b8e142 X1 X1
               have r₂ := b8e133 X1 X1
               grind)
            | exact resolve b8e142 b8e133
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133 b8e142
          have b8e247 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e147 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e147 X0 X1
               grind)
            | exact superpose b8e147 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e147 X1 X0
               grind)
            | (have r₁ := b8e16 X1 X0
               have r₂ := b8e147 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e147 X1 X1
               grind)
            | exact resolve b8e16 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e249 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e147 (σ X0) (σ X1)
               grind)
            | exact superpose b8e147 b8e19
            | (have j1 := b8e147 (σ X0) (σ X1)
               grind)
            | exact resolve b8e19 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e254 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 X1
               have i₂ := b8e147 (τ X0) X1
               grind)
            | exact superpose b8e147 b8e26
            | (have j1 := b8e147 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e147
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e255 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b8e247 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e247
          have b8e260 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e249 X0 X1
               have i₂ := b8e77 X1
               grind)
            | exact superpose b8e77 b8e249
            | (have j0 := b8e249 X0 X1
               grind)
            | exact resolve b8e249 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e249
          have b8e1811 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ X0)) ∨ (M.op X0 (τ X1)) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e255 (τ X1) X0
               grind)
            | exact superpose b8e255 b8e25
            | (have j1 := b8e255 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
          have b8e1818 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e30 X1 X0
               have i₂ := b8e255 X1 (σ X0)
               grind)
            | exact superpose b8e255 b8e30
            | (have j1 := b8e255 X1 (σ X0)
               grind)
            | exact resolve b8e30 b8e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e255
          have b8e1895 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1818 X0 X1
               have i₂ := b8e77 X0
               grind)
            | exact superpose b8e77 b8e1818
            | (have j0 := b8e1818 X0 X1
               grind)
            | exact resolve b8e1818 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1818
          have b8e1904 : ∀ X0 X1 : G, (M.op X0 X0) = (k (τ X1) X0) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1895 X0 X1
               have i₂ := b8e14 (M.op X0 X0)
               grind)
            | exact superpose b8e14 b8e1895
            | (have j0 := b8e1895 X0 X1
               grind)
            | exact resolve b8e1895 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1895
          have b8e10588 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e254 (σ X0) X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e254
            | exact resolve b8e254 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e254
          have b8e10847 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e10588 X0 X1
               have i₂ := b8e19 X1 X0
               grind)
            | exact superpose b8e19 b8e10588
            | (have j0 := b8e10588 X0 X1
               grind)
            | exact resolve b8e10588 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10588
          have b8e17000 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 (σ X1) (σ X0)
               have i₂ := b8e260 X0 X1
               grind)
            | exact superpose b8e260 b8e17
            | (have j0 := b8e17 (σ X0) (σ X1)
               have j1 := b8e260 X1 X0
               grind)
            | exact resolve b8e17 b8e260
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e17059 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e260 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e260
          have b8e17080 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17000 X0 X1
               have i₂ := b8e77 X1
               grind)
            | exact superpose b8e77 b8e17000
            | (have j0 := b8e17000 X0 X1
               grind)
            | exact resolve b8e17000 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17000
          have b8e17179 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17080 X0 X1
               have i₂ := b8e77 X0
               grind)
            | exact superpose b8e77 b8e17080
            | (have j0 := b8e17080 X0 X1
               grind)
            | exact resolve b8e17080 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17080
          have b8e17228 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e17179 X0 X1
               have j1 := b8e17059 X1 X0
               grind)
            | (have r₁ := b8e17179 X1 X0
               have r₂ := b8e17059 X0 X1
               grind)
            | exact resolve b8e17179 b8e17059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17179
          have b8e17249 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17228 X0 X1
               have i₂ := b8e77 X0
               grind)
            | exact superpose b8e77 b8e17228
            | (have j0 := b8e17228 X0 X1
               grind)
            | exact resolve b8e17228 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17228
          have b8e17258 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e17249 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e17249
            | (have j0 := b8e17249 X0 X1
               grind)
            | exact resolve b8e17249 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17249
          have b8e17260 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e17258 X0 X1
               have j1 := b8e17059 X1 X0
               grind)
            | (have r₁ := b8e17258 X1 X0
               have r₂ := b8e17059 X0 X1
               grind)
            | exact resolve b8e17258 b8e17059
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17059 b8e17258
          have b8e19362 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e16 X0 X1
               have i₂ := b8e10847 X1 X0
               grind)
            | (have i₁ := b8e16 X1 X1
               have i₂ := b8e10847 X0 X1
               grind)
            | exact superpose b8e10847 b8e16
            | (have j0 := b8e16 X0 X0
               have j1 := b8e10847 X1 X0
               grind)
            | (have r₁ := b8e16 X1 X0
               have r₂ := b8e10847 X0 X1
               grind)
            | (have r₁ := b8e16 X1 X1
               have r₂ := b8e10847 X1 X1
               grind)
            | exact resolve b8e16 b8e10847
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e10847
          have b8e19434 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (σ (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have j0 := b8e19362 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19362
          have b8e28465 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e1904 X1 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e1904
            | (have j0 := b8e1904 X1 (σ X0)
               grind)
            | exact resolve b8e1904 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1904
          have b8e28808 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (k X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e28465 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e28465
            | (have j0 := b8e28465 X0 X1
               grind)
            | exact resolve b8e28465 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28465
          have b8e49073 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op x x) = (k y x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e28808 y x
               grind)
            | exact superpose b8e28808 b8e20
            | (have j1 := b8e28808 y x
               grind)
            | exact resolve b8e20 b8e28808
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28808
          have b8e49751 : (M.op x x) = (k y x) := by
            first
            | (have j1 := b8e19434 y x
               grind)
            | (have r₁ := b8e49073
               have r₂ := b8e19434 y x
               grind)
            | exact resolve b8e49073 b8e19434
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19434 b8e49073
          have b8e51765 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e147 x y
               have i₂ := b8e49751
               grind)
            | exact superpose b8e49751 b8e147
            | (have j0 := b8e147 x y
               grind)
            | exact resolve b8e147 b8e49751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147
          have b8e192248 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X1))) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e26 X0 (τ X1)
               have i₂ := b8e1811 (τ X0) X1
               grind)
            | exact superpose b8e1811 b8e26
            | (have j1 := b8e1811 (τ X0) X1
               grind)
            | exact resolve b8e26 b8e1811
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26 b8e1811
          have b8e192249 : ∀ X0 X1 : G, (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e192248 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e192248
            | (have j0 := b8e192248 X0 X1
               grind)
            | exact resolve b8e192248 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192248
          have b8e192276 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X0))) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e192249 X0 X1
               have i₂ := b8e80 X0
               grind)
            | exact superpose b8e80 b8e192249
            | (have j0 := b8e192249 X0 X1
               grind)
            | exact resolve b8e192249 b8e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80 b8e192249
          have b8e192285 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b8e192276 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e192276
            | (have j0 := b8e192276 X0 X1
               grind)
            | exact resolve b8e192276 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192276
          have b8e194124 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) (τ (σ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e192285 (σ X1) (σ X0)
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e192285
            | exact resolve b8e192285 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192285
          have b8e194297 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) (τ (σ X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b8e194124 X0 X1
               have i₂ := b8e77 X1
               grind)
            | exact superpose b8e77 b8e194124
            | (have j0 := b8e194124 X0 X1
               grind)
            | exact resolve b8e194124 b8e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77 b8e194124
          have b8e194306 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (τ (σ X1)) X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e194297 X0 X1
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e194297
            | (have j0 := b8e194297 X0 X1
               grind)
            | exact resolve b8e194297 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194297
          have b8e194309 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e194306 X0 X1
               have i₂ := b8e14 X1
               grind)
            | exact superpose b8e14 b8e194306
            | (have j0 := b8e194306 X0 X1
               grind)
            | exact resolve b8e194306 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194306
          have b8e237314 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X1 X0)) ∨ (σ (k X0 X1)) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e194309 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e194309
          have b8e256452 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e237314 y y
               have i₂ := b8e51765
               grind)
            | exact superpose b8e51765 b8e237314
            | exact resolve b8e237314 b8e51765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e51765 b8e237314
          have b8e256463 : (σ (M.op x y)) = (σ (k y y)) ∨ (M.op x y) = (M.op x x) := by grind
          clear b8e256452
          have b8e256471 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e256463
               have i₂ := b8e65 y
               grind)
            | exact superpose b8e65 b8e256463
            | exact resolve b8e256463 b8e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e65 b8e256463
          have b8e313859 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b8e17260 y x
               have i₂ := b8e49751
               grind)
            | exact superpose b8e49751 b8e17260
            | (have j0 := b8e17260 y x
               grind)
            | exact resolve b8e17260 b8e49751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e17260
          have b8e313872 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
          clear b8e313859
          have b8e314525 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e313872
               grind)
            | exact superpose b8e313872 b8e20
            | exact resolve b8e20 b8e313872
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e313872
          have b8e315333 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b8e314525
               have i₂ := b8e256471
               grind)
            | exact superpose b8e256471 b8e314525
            | (have r₁ := b8e314525
               have r₂ := b8e256471
               grind)
            | exact resolve b8e314525 b8e256471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256471
          have b8e315335 : (M.op x y) = (M.op x x) := by grind
          clear b8e315333
          have b8e316275 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e315335
               grind)
            | exact superpose b8e315335 b8e17
            | (have j0 := b8e17 x x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e315335
               grind)
            | exact resolve b8e17 b8e315335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e316353 : (M.op x x) = (M.op y y) ∨ (M.op y y) = (k y x) := by grind
          clear b8e316275
          have b8e316405 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
            first
            | (have i₁ := b8e316353
               have i₂ := b8e49751
               grind)
            | exact superpose b8e49751 b8e316353
            | exact resolve b8e316353 b8e49751
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49751 b8e316353
          have b8e316406 : (M.op x x) = (M.op y y) := by grind
          clear b8e316405
          have b8e317174 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e314525
               have i₂ := b8e316406
               grind)
            | exact superpose b8e316406 b8e314525
            | exact resolve b8e314525 b8e316406
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e314525 b8e316406
          have b8e317384 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e317174
               have i₂ := b8e315335
               grind)
            | exact superpose b8e315335 b8e317174
            | exact resolve b8e317174 b8e315335
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e315335 b8e317174
          have b8e317385 : False := by grind
          exact b8e317385

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
        have b1e48 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e49 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e50 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e49
             have r₂ := b1e23
             grind)
          | exact resolve b1e49 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e50
          | exact resolve b1e50 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e52 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e51
          | exact resolve b1e51 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e51
        have b1e53 : False := by grind
        exact b1e53
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
        have b2e54 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e245 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e54 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e1612 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e245 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e245
          | (have j0 := b2e245 x y
             grind)
          | exact resolve b2e245 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e245
        have b2e1617 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e1612
        have b2e1622 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1617
             have r₂ := b2e22
             grind)
          | exact resolve b2e1617 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1617
        have b2e1626 : False := by grind
        exact b2e1626
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
        have b3e48 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        clear b3e48
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
          have b5e46 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e48 : x = y ∨ x = (k x y) := by grind
          clear b5e46
          have b5e49 : x = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e25
               grind)
            | exact resolve b5e48 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e48
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e256 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e1547 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e256 x y
               have i₂ := b5e49
               grind)
            | exact superpose b5e49 b5e256
            | (have j0 := b5e256 x y
               grind)
            | exact resolve b5e256 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e256
          have b5e1552 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e1547
          have b5e1557 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1552
               have r₂ := b5e24
               grind)
            | exact resolve b5e1552 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1552
          have b5e1561 : False := by grind
          exact b5e1561
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
        have b6e51 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e53 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e51
        have b6e56 : x = (M.op x y) := by
          first
          | (have r₁ := b6e53
             have r₂ := b6e21
             grind)
          | exact resolve b6e53 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e59 : False := by grind
        exact b6e59
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
          have b7e41 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          clear b7e41
          have b7e45 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e44
               have r₂ := b7e25
               grind)
            | exact resolve b7e44 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e44
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
          have b7e60 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e61 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e60
          have b7e63 : y = (M.op x y) := by
            first
            | (have r₁ := b7e61
               have r₂ := b7e21
               grind)
            | exact resolve b7e61 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e65 : False := by grind
          exact b7e65
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
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e224 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e47 x y
               grind)
            | exact superpose b8e47 b8e20
            | (have j1 := b8e47 x y
               grind)
            | exact resolve b8e20 b8e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e47
          have b8e246 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e224
               have r₂ := b8e24
               grind)
            | exact resolve b8e224 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e224
          have b8e249 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e246
               have r₂ := b8e23
               grind)
            | exact resolve b8e246 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e246
          have b8e250 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e249
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e249
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e249 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e249
          have b8e251 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e250
          have b8e252 : x = (M.op x y) := by
            first
            | (have r₁ := b8e251
               have r₂ := b8e22
               grind)
            | exact resolve b8e251 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251
          have b8e253 : False := by grind
          exact b8e253

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation3888 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3888 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
      have b0e60 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e63 : False := by grind
      exact b0e63
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
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e256 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b4e268 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e256
               have r₂ := b4e23
               grind)
            | exact resolve b4e256 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e256
          have b4e1140 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e268
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e268
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e268
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e268
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e268 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1141 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e1140
          have b4e1142 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1141
               have r₂ := b4e21
               grind)
            | exact resolve b4e1141 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1141
          have b4e1144 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1142
               grind)
            | exact superpose b4e1142 b4e20
            | exact resolve b4e20 b4e1142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1148 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e1142
               grind)
            | exact superpose b4e1142 b4e17
            | (have j0 := b4e17 (σ x) (σ y)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e1142
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e1142
               grind)
            | exact resolve b4e17 b4e1142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1142
          have b4e1157 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e1148
          have b4e1166 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e1157
               have r₂ := b4e23
               grind)
            | exact resolve b4e1157 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1157
          have b4e1178 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e1166
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e1166
            | exact resolve b4e1166 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1166
          have b4e1429 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b4e1178
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e1178
            | (have j1 := b4e18 y x
               grind)
            | exact resolve b4e1178 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1178
          have b4e1450 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b4e1429
          have b4e1467 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b4e1450
               have r₂ := b4e1144
               grind)
            | exact resolve b4e1450 b4e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1144 b4e1450
          have b4e1469 : x = (M.op x y) := by
            first
            | (have r₁ := b4e1467
               have r₂ := b4e21
               grind)
            | exact resolve b4e1467 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1467
          have b4e1654 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e1469
               grind)
            | exact superpose b4e1469 b4e17
            | (have j0 := b4e17 x y
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e1469
               grind)
            | exact resolve b4e17 b4e1469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1664 : x = y ∨ x = (k y x) := by grind
          clear b4e1654
          have b4e1669 : x = (k y x) := by
            first
            | (have r₁ := b4e1664
               have r₂ := b4e21
               grind)
            | exact resolve b4e1664 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1664
          have b4e1709 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e268
               have i₂ := b4e1669
               grind)
            | exact superpose b4e1669 b4e268
            | exact resolve b4e268 b4e1669
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e268 b4e1669
          have b4e1713 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e1709
               have i₂ := b4e1469
               grind)
            | exact superpose b4e1469 b4e1709
            | exact resolve b4e1709 b4e1469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1709
          have b4e1714 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e1713
          have b4e1774 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e1714
               grind)
            | exact superpose b4e1714 b4e20
            | exact resolve b4e20 b4e1714
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1714
          have b4e1804 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e1774
               have i₂ := b4e1469
               grind)
            | exact superpose b4e1469 b4e1774
            | exact resolve b4e1774 b4e1469
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1469 b4e1774
          have b4e1805 : False := by grind
          exact b4e1805
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e21 : x ≠ y := by grind
          have b5e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b5e202 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e44 x y
               grind)
            | exact superpose b5e44 b5e20
            | (have j1 := b5e44 x y
               grind)
            | exact resolve b5e20 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e213 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e202
               have r₂ := b5e23
               grind)
            | exact resolve b5e202 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e202
          have b5e1208 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e213
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e213
            | (have j1 := b5e18 y x
               grind)
            | (have r₁ := b5e213
               have r₂ := b5e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b5e213
               have r₂ := b5e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b5e213 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1209 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e1208
          have b5e1210 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e1209
               have r₂ := b5e21
               grind)
            | exact resolve b5e1209 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1209
          have b5e1212 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1210
               grind)
            | exact superpose b5e1210 b5e20
            | exact resolve b5e20 b5e1210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1216 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e17 (σ y) (σ x)
               have i₂ := b5e1210
               grind)
            | exact superpose b5e1210 b5e17
            | (have j0 := b5e17 (σ x) (σ y)
               grind)
            | (have r₁ := b5e17 (σ y) (σ x)
               have r₂ := b5e1210
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e1210
               grind)
            | exact resolve b5e17 b5e1210
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1210
          have b5e1226 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b5e1216
          have b5e1236 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b5e1226
               have r₂ := b5e23
               grind)
            | exact resolve b5e1226 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1226
          have b5e1249 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b5e1236
               have i₂ := b5e19 y x
               grind)
            | exact superpose b5e19 b5e1236
            | exact resolve b5e1236 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1236
          have b5e1642 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b5e1249
               have i₂ := b5e18 y x
               grind)
            | exact superpose b5e18 b5e1249
            | (have j1 := b5e18 y x
               grind)
            | exact resolve b5e1249 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1249
          have b5e1664 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b5e1642
          have b5e1682 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b5e1664
               have r₂ := b5e1212
               grind)
            | exact resolve b5e1664 b5e1212
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1212 b5e1664
          have b5e1685 : x = (M.op x y) := by
            first
            | (have r₁ := b5e1682
               have r₂ := b5e21
               grind)
            | exact resolve b5e1682 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1682
          have b5e1729 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b5e17 y x
               have i₂ := b5e1685
               grind)
            | exact superpose b5e1685 b5e17
            | (have j0 := b5e17 x y
               grind)
            | (have r₁ := b5e17 y x
               have r₂ := b5e1685
               grind)
            | exact resolve b5e17 b5e1685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e1740 : x = y ∨ x = (k y x) := by grind
          clear b5e1729
          have b5e1746 : x = (k y x) := by
            first
            | (have r₁ := b5e1740
               have r₂ := b5e21
               grind)
            | exact resolve b5e1740 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1740
          have b5e1811 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e213
               have i₂ := b5e1746
               grind)
            | exact superpose b5e1746 b5e213
            | exact resolve b5e213 b5e1746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e213 b5e1746
          have b5e1815 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1811
               have i₂ := b5e1685
               grind)
            | exact superpose b5e1685 b5e1811
            | exact resolve b5e1811 b5e1685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1811
          have b5e1816 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e1815
          have b5e1876 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e1816
               grind)
            | exact superpose b5e1816 b5e20
            | exact resolve b5e20 b5e1816
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1816
          have b5e1908 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e1876
               have i₂ := b5e1685
               grind)
            | exact superpose b5e1685 b5e1876
            | exact resolve b5e1876 b5e1685
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1685 b5e1876
          have b5e1909 : False := by grind
          exact b5e1909
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
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
          have b7e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e47 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e45
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
          have b7e63 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e53
               grind)
            | exact superpose b7e53 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e53
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e53
          have b7e64 : y = (M.op y x) ∨ x = y := by grind
          clear b7e63
          have b7e66 : x = y := by
            first
            | (have r₁ := b7e64
               have r₂ := b7e22
               grind)
            | exact resolve b7e64 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64
          have b7e68 : False := by grind
          exact b7e68
        · have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e177 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e56 x y
               grind)
            | exact superpose b8e56 b8e20
            | (have j1 := b8e56 x y
               grind)
            | exact resolve b8e20 b8e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e188 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e177
               have r₂ := b8e23
               grind)
            | exact resolve b8e177 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e177
          have b8e1000 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e188
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e188
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e188
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e188
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e188 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1001 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e1000
          have b8e1002 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e1001
               have r₂ := b8e21
               grind)
            | exact resolve b8e1001 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1001
          have b8e1004 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1002
               grind)
            | exact superpose b8e1002 b8e20
            | exact resolve b8e20 b8e1002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1008 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e1002
               grind)
            | exact superpose b8e1002 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e1002
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1002
               grind)
            | exact resolve b8e17 b8e1002
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1002
          have b8e1017 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e1008
          have b8e1026 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e1017
               have r₂ := b8e23
               grind)
            | exact resolve b8e1017 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1017
          have b8e1038 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e1026
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e1026
            | exact resolve b8e1026 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1026
          have b8e1389 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e1038
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e1038
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e1038 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1038
          have b8e1411 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by grind
          clear b8e1389
          have b8e1429 : x = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e1411
               have r₂ := b8e1004
               grind)
            | exact resolve b8e1411 b8e1004
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1004 b8e1411
          have b8e1432 : x = (M.op x y) := by
            first
            | (have r₁ := b8e1429
               have r₂ := b8e21
               grind)
            | exact resolve b8e1429 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1429
          have b8e1492 : x ≠ x ∨ x = y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e1432
               grind)
            | exact superpose b8e1432 b8e17
            | (have j0 := b8e17 x y
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e1432
               grind)
            | exact resolve b8e17 b8e1432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1502 : x = y ∨ x = (k y x) := by grind
          clear b8e1492
          have b8e1507 : x = (k y x) := by
            first
            | (have r₁ := b8e1502
               have r₂ := b8e21
               grind)
            | exact resolve b8e1502 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1502
          have b8e1565 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e188
               have i₂ := b8e1507
               grind)
            | exact superpose b8e1507 b8e188
            | exact resolve b8e188 b8e1507
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e188 b8e1507
          have b8e1569 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e1565
               have i₂ := b8e1432
               grind)
            | exact superpose b8e1432 b8e1565
            | exact resolve b8e1565 b8e1432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1565
          have b8e1570 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e1569
          have b8e1631 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1570
               grind)
            | exact superpose b8e1570 b8e20
            | exact resolve b8e20 b8e1570
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1570
          have b8e1661 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e1631
               have i₂ := b8e1432
               grind)
            | exact superpose b8e1432 b8e1631
            | exact resolve b8e1631 b8e1432
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1432 b8e1631
          have b8e1662 : False := by grind
          exact b8e1662

/-- `Equation4164`: `x ◇ y = ((y ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation4164 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e33 : (M.op x y) = (k x y) := by grind
      have b0e34 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      have b0e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e34
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e34
        | exact resolve b0e34 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34
      have b0e37 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e36
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e36
        | exact resolve b0e36 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e36
      have b0e38 : False := by grind
      exact b0e38
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e31 : (M.op x y) = (k x y) := by grind
        have b1e56 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b1e68 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e56
             have r₂ := b1e21
             grind)
          | exact resolve b1e56 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e69 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e68
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e68
          | exact resolve b1e68 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e68
        have b1e70 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e69
             have i₂ := b1e31
             grind)
          | exact superpose b1e31 b1e69
          | exact resolve b1e69 b1e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e31 b1e69
        have b1e71 : False := by grind
        exact b1e71
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e42 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e57 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b2e59 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b2e57 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e240 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e59 X0
             have i₂ := b2e42 X0 X1
             grind)
          | (have i₁ := b2e59 X0
             have i₂ := b2e42 X0 (M.op X0 X0)
             grind)
          | exact superpose b2e42 b2e59
          | (have j1 := b2e42 X1 X0
             grind)
          | exact resolve b2e59 b2e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42 b2e59
        have b2e258 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e240 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e240
        have b2e331 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e258 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e258
        have b2e332 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e331 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e331
        have b2e431 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e332 (σ X0)
             grind)
          | exact superpose b2e332 b2e18
          | exact resolve b2e18 b2e332
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e438 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e431 X0
             have i₂ := b2e332 X0
             grind)
          | exact superpose b2e332 b2e431
          | exact resolve b2e431 b2e332
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e332 b2e431
        have b2e635 : (σ y) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e438 x
             grind)
          | exact superpose b2e438 b2e21
          | exact resolve b2e21 b2e438
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e438
        have b2e654 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e635
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e635
          | exact resolve b2e635 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e635
        have b2e655 : False := by grind
        exact b2e655
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e32 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        have b3e33 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e32
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e32
          | exact resolve b3e32 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e55 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
        have b3e66 : (M.op x y) = (k x y) := by
          first
          | (have r₁ := b3e55
             have r₂ := b3e20
             grind)
          | exact resolve b3e55 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e86 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e33
             grind)
          | exact superpose b3e33 b3e19
          | exact resolve b3e19 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33
        have b3e87 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e86
             have i₂ := b3e66
             grind)
          | exact superpose b3e66 b3e86
          | exact resolve b3e86 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e66 b3e86
        have b3e88 : False := by grind
        exact b3e88
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e65 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
          have b4e66 : y = (M.op x x) ∨ (M.op x y) = (k x y) := by grind
          have b4e77 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e66
               have r₂ := b4e21
               grind)
            | exact resolve b4e66 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e78 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e65
               have r₂ := b4e23
               grind)
            | exact resolve b4e65 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e65
          have b4e79 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e78
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e78
            | exact resolve b4e78 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e80 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e79
               have i₂ := b4e77
               grind)
            | exact superpose b4e77 b4e79
            | exact resolve b4e79 b4e77
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77 b4e79
          have b4e81 : False := by grind
          exact b4e81
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e49 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e65 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b5e67 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b5e65 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65
          have b5e238 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e67 X0
               have i₂ := b5e49 X0 X1
               grind)
            | (have i₁ := b5e67 X0
               have i₂ := b5e49 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e49 b5e67
            | (have j1 := b5e49 X1 X0
               grind)
            | exact resolve b5e67 b5e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49 b5e67
          have b5e254 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e238 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e238
          have b5e322 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e254 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e254
          have b5e323 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e322 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e322
          have b5e420 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e323 (σ X0)
               grind)
            | exact superpose b5e323 b5e19
            | exact resolve b5e19 b5e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e427 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e420 X0
               have i₂ := b5e323 X0
               grind)
            | exact superpose b5e323 b5e420
            | exact resolve b5e420 b5e323
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e323 b5e420
          have b5e626 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e427 y
               grind)
            | exact superpose b5e427 b5e24
            | exact resolve b5e24 b5e427
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e427
          have b5e644 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e626
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e626
            | exact resolve b5e626 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e626
          have b5e645 : False := by grind
          exact b5e645
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e55 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e71 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          grind
        have b6e73 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
          intro X0
          first
          | (have j0 := b6e71 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e253 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e73 X0
             have i₂ := b6e55 X0 X1
             grind)
          | (have i₁ := b6e73 X0
             have i₂ := b6e55 X0 (M.op X0 X0)
             grind)
          | exact superpose b6e55 b6e73
          | (have j1 := b6e55 X1 X0
             grind)
          | exact resolve b6e73 b6e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e55 b6e73
        have b6e270 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e253 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e253
        have b6e843 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e270 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e270
        have b6e844 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e843 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e843
        have b6e1157 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e844 (σ X0)
             grind)
          | exact superpose b6e844 b6e18
          | exact resolve b6e18 b6e844
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1164 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e1157 X0
             have i₂ := b6e844 X0
             grind)
          | exact superpose b6e844 b6e1157
          | exact resolve b6e1157 b6e844
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e844 b6e1157
        have b6e1645 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e1164 x
             grind)
          | exact superpose b6e1164 b6e22
          | exact resolve b6e22 b6e1164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1164
        have b6e1910 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op x x)
             have i₂ := b6e1645
             grind)
          | exact superpose b6e1645 b6e13
          | exact resolve b6e13 b6e1645
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1645
        have b6e1929 : y = (M.op x x) := by
          first
          | (have i₁ := b6e1910
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1910
          | exact resolve b6e1910 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1910
        have b6e1934 : False := by grind
        exact b6e1934
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e58 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e83 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            grind
          have b7e85 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
            intro X0
            first
            | (have j0 := b7e83 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e250 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b7e85 X0
               have i₂ := b7e58 X0 X1
               grind)
            | (have i₁ := b7e85 X0
               have i₂ := b7e58 X0 (M.op X0 X0)
               grind)
            | exact superpose b7e58 b7e85
            | (have j1 := b7e58 X1 X0
               grind)
            | exact resolve b7e85 b7e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e58 b7e85
          have b7e266 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e250 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e250
          have b7e546 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e266 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e266
          have b7e547 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e546 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e546
          have b7e656 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e547 (σ X0)
               grind)
            | exact superpose b7e547 b7e19
            | exact resolve b7e19 b7e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e663 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e656 X0
               have i₂ := b7e547 X0
               grind)
            | exact superpose b7e547 b7e656
            | exact resolve b7e656 b7e547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e547 b7e656
          have b7e924 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e663 y
               grind)
            | exact superpose b7e663 b7e24
            | exact resolve b7e24 b7e663
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e663
          have b7e1674 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e924
               grind)
            | exact superpose b7e924 b7e14
            | exact resolve b7e14 b7e924
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e924
          have b7e1693 : x = (M.op y y) := by
            first
            | (have i₁ := b7e1674
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e1674
            | exact resolve b7e1674 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e1674
          have b7e1698 : False := by grind
          exact b7e1698
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b8e60 : ∀ X0 : G, (σ x) ≠ X0 ∨ (M.op X0 X0) = (σ y) ∨ (k (σ y) X0) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ y) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ y) (σ y))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 (σ y) X0
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
          have b8e253 : (σ y) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have j0 := b8e60 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e60
          have b8e254 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
            first
            | (have r₁ := b8e253
               have r₂ := b8e23
               grind)
            | exact resolve b8e253 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e255 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
            first
            | (have i₁ := b8e254
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e254
            | exact resolve b8e254 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e254
          have b8e256 : (σ (M.op x y)) ≠ (σ (k y x)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e255
               grind)
            | exact superpose b8e255 b8e20
            | exact resolve b8e20 b8e255
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e255
          have b8e335 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e256
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e256
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e256 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e256
          have b8e341 : x = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e335
          have b8e344 : y = (M.op x x) := by
            first
            | (have r₁ := b8e341
               have r₂ := b8e22
               grind)
            | exact resolve b8e341 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e341
          have b8e345 : False := by grind
          exact b8e345

/-- `Equation4164`: `x ◇ y = ((y ◇ y) ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation4164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
      have b0e27 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e53 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e27 X0 X1
           have i₂ := b0e16 X1 (τ X0)
           grind)
        | exact superpose b0e16 b0e27
        | (have j1 := b0e16 X1 (τ X0)
           grind)
        | exact resolve b0e27 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e27
      have b0e55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e134 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
      have b0e141 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e142 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e315 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e53 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e53
        | exact resolve b0e53 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e346 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e315 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e315
        | (have j0 := b0e315 X0 X1
           grind)
        | exact resolve b0e315 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e315
      have b0e446 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e141 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e141
        | (have j0 := b0e141 (τ X1) (τ X0)
           grind)
        | exact resolve b0e141 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e455 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e446 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e446
        | (have j0 := b0e446 X0 X1
           grind)
        | exact resolve b0e446 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e446
      have b0e458 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e455 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e455
        | (have j0 := b0e455 X0 X1
           grind)
        | exact resolve b0e455 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e455
      have b0e460 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e458 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e458
        | (have j0 := b0e458 X0 X1
           grind)
        | exact resolve b0e458 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e458
      have b0e461 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e460 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e460
        | (have j0 := b0e460 X0 X1
           grind)
        | exact resolve b0e460 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e460
      have b0e462 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e461 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e461
        | (have j0 := b0e461 X0 X1
           grind)
        | exact resolve b0e461 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e461
      have b0e463 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e462 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e462
        | (have j0 := b0e462 X0 X1
           grind)
        | exact resolve b0e462 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e462
      have b0e478 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e142 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e142
        | (have j0 := b0e142 (τ X1) (τ X0)
           grind)
        | exact resolve b0e142 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e486 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e478 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e478
        | (have j0 := b0e478 X0 X1
           grind)
        | exact resolve b0e478 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e478
      have b0e489 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e486 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e486
        | (have j0 := b0e486 X0 X1
           grind)
        | exact resolve b0e486 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e486
      have b0e491 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e489 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e489
        | (have j0 := b0e489 X0 X1
           grind)
        | exact resolve b0e489 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e489
      have b0e492 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e491 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e491
        | (have j0 := b0e491 X0 X1
           grind)
        | exact resolve b0e491 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e491
      have b0e493 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e492 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e492
        | (have j0 := b0e492 X0 X1
           grind)
        | exact resolve b0e492 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e492
      have b0e494 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e493 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e493
        | (have j0 := b0e493 X0 X1
           grind)
        | exact resolve b0e493 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e493
      have b0e557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e134
           have i₂ := b0e346 x y
           grind)
        | exact superpose b0e346 b0e134
        | (have j1 := b0e346 (σ x) (σ y)
           grind)
        | (have r₁ := b0e134
           have r₂ := b0e346 x y
           grind)
        | exact resolve b0e134 b0e346
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134 b0e346
      have b0e558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e557
      have b0e30818 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e558
           grind)
        | exact superpose b0e558 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e558
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e558
           grind)
        | exact resolve b0e14 b0e558
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e558
      have b0e30820 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e30818
      have b0e30821 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e30820
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e30820
        | exact resolve b0e30820 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30820
      have b0e31970 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e30821
           grind)
        | exact superpose b0e30821 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e30821
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e30821
           grind)
        | exact resolve b0e15 b0e30821
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31971 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e30821
           grind)
        | exact superpose b0e30821 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e30821
           grind)
        | exact resolve b0e14 b0e30821
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30821
      have b0e31972 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e31970
      have b0e31978 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e31971
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e31971
        | exact resolve b0e31971 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31971
      have b0e31979 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e31978
      have b0e31980 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e31972
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e31972
        | exact resolve b0e31972 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31972
      have b0e31982 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e31980
           have r₂ := b0e31979
           grind)
        | exact resolve b0e31980 b0e31979
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31979 b0e31980
      have b0e33207 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e31982
           grind)
        | exact superpose b0e31982 b0e12
        | exact resolve b0e12 b0e31982
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31982
      have b0e33384 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e33207
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e33207
        | exact resolve b0e33207 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33207
      have b0e33385 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e494 y x
           grind)
        | (have r₁ := b0e33384
           have r₂ := b0e494 y x
           grind)
        | exact resolve b0e33384 b0e494
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e494 b0e33384
      have b0e33810 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e33385
           grind)
        | exact superpose b0e33385 b0e12
        | exact resolve b0e12 b0e33385
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33385
      have b0e33990 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e33810
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e33810
        | exact resolve b0e33810 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33810
      have b0e33991 : y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e463 y x
           grind)
        | (have r₁ := b0e33990
           have r₂ := b0e463 y x
           grind)
        | exact resolve b0e33990 b0e463
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e463 b0e33990
      have b0e34360 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e33991
           grind)
        | exact superpose b0e33991 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e33991
           grind)
        | exact resolve b0e14 b0e33991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e34361 : x ≠ y ∨ x = (M.op x y) := by grind
      have b0e34362 : x = (k y x) ∨ x = (M.op x y) := by grind
      clear b0e34360
      have b0e35189 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e141 x y
           have i₂ := b0e34362
           grind)
        | exact superpose b0e34362 b0e141
        | (have j0 := b0e141 x y
           grind)
        | exact resolve b0e141 b0e34362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141
      have b0e35258 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e35189
      have b0e42992 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e35258
           grind)
        | exact superpose b0e35258 b0e18
        | exact resolve b0e18 b0e35258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35258
      have b0e44116 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e42992
           have i₂ := b0e33991
           grind)
        | exact superpose b0e33991 b0e42992
        | exact resolve b0e42992 b0e33991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42992
      have b0e44119 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
      clear b0e44116
      have b0e44120 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e44119
           have r₂ := b0e34361
           grind)
        | exact resolve b0e44119 b0e34361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44119
      have b0e44170 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e44120
           grind)
        | exact superpose b0e44120 b0e18
        | exact resolve b0e18 b0e44120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e44174 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e44120
           grind)
        | exact superpose b0e44120 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e44120
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e44120
           grind)
        | exact resolve b0e15 b0e44120
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44120
      have b0e44176 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
      clear b0e44174
      have b0e44183 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e44176
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e44176
        | exact resolve b0e44176 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44176
      have b0e44469 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e44170
           have i₂ := b0e33991
           grind)
        | exact superpose b0e33991 b0e44170
        | exact resolve b0e44170 b0e33991
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33991 b0e44170
      have b0e44473 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e44469
           have r₂ := b0e34361
           grind)
        | exact resolve b0e44469 b0e34361
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34361 b0e44469
      have b0e45063 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e44183
           have i₂ := b0e34362
           grind)
        | exact superpose b0e34362 b0e44183
        | exact resolve b0e44183 b0e34362
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e34362 b0e44183
      have b0e45244 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
      clear b0e45063
      have b0e45396 : x = (M.op x y) := by
        first
        | (have r₁ := b0e45244
           have r₂ := b0e44473
           grind)
        | exact resolve b0e45244 b0e44473
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44473 b0e45244
      have b0e45492 : x ≠ x ∨ x = y ∨ y = (k y x) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e45396
           grind)
        | exact superpose b0e45396 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e45396
           grind)
        | exact resolve b0e15 b0e45396
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45493 : x ≠ y ∨ x = (k y x) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e45396
           grind)
        | exact superpose b0e45396 b0e14
        | (have j0 := b0e14 y x
           grind)
        | exact resolve b0e14 b0e45396
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45494 : y = (k y x) ∨ x = y := by grind
      clear b0e45492
      have b0e45778 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e142 x y
           have i₂ := b0e45494
           grind)
        | exact superpose b0e45494 b0e142
        | (have j0 := b0e142 x y
           grind)
        | exact resolve b0e142 b0e45494
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142
      have b0e45816 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e45778
      have b0e48006 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e45816
           grind)
        | exact superpose b0e45816 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e45816
           grind)
        | exact resolve b0e14 b0e45816
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45816
      have b0e48008 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
      clear b0e48006
      have b0e48009 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e48008
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e48008
        | exact resolve b0e48008 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48008
      have b0e48443 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e48009
           grind)
        | exact superpose b0e48009 b0e18
        | exact resolve b0e18 b0e48009
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48009
      have b0e48459 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
        first
        | (have i₁ := b0e48443
           have i₂ := b0e45396
           grind)
        | exact superpose b0e45396 b0e48443
        | exact resolve b0e48443 b0e45396
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48443
      have b0e48460 : (σ x) = (σ (k y x)) ∨ x = y := by grind
      clear b0e48459
      have b0e48948 : (k y x) = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e48460
           grind)
        | exact superpose b0e48460 b0e12
        | exact resolve b0e12 b0e48460
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48460
      have b0e49176 : x = (k y x) ∨ x = y := by
        first
        | (have i₁ := b0e48948
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e48948
        | exact resolve b0e48948 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e48948
      have b0e49177 : x = (k y x) := by
        first
        | (have r₁ := b0e49176
           have r₂ := b0e45493
           grind)
        | exact resolve b0e49176 b0e45493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45493 b0e49176
      have b0e49663 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e45494
           have i₂ := b0e49177
           grind)
        | exact superpose b0e49177 b0e45494
        | exact resolve b0e45494 b0e49177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45494 b0e49177
      have b0e49706 : x = y := by grind
      clear b0e49663
      have b0e50094 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e49706
           grind)
        | exact superpose b0e49706 b0e18
        | exact resolve b0e18 b0e49706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50096 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e49706
           grind)
        | exact superpose b0e49706 b0e20
        | exact resolve b0e20 b0e49706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50140 : x = (M.op x x) := by
        first
        | (have i₁ := b0e45396
           have i₂ := b0e49706
           grind)
        | exact superpose b0e49706 b0e45396
        | exact resolve b0e45396 b0e49706
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45396 b0e49706
      have b0e50184 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e50094
           have i₂ := b0e50140
           grind)
        | exact superpose b0e50140 b0e50094
        | exact resolve b0e50094 b0e50140
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50094 b0e50140
      have b0e50185 : False := by grind
      exact b0e50185
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b1e24 : x ≠ x ∨ y = (k x y) := by
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
        have b1e26 : y = (k x y) := by grind
        clear b1e24
        have b1e35 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e37 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e35
        have b1e38 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e37
             have r₂ := b1e23
             grind)
          | exact resolve b1e37 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e37
        have b1e39 : (σ x) = (σ (k x y)) := by
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : x ≠ x ∨ y = (k x y) := by
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
        have b2e24 : y = (k x y) := by grind
        clear b2e23
        have b2e45 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e436 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e121 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e121
          | (have j0 := b2e121 y x
             grind)
          | exact resolve b2e121 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e121
        have b2e439 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e436
        have b2e442 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e439
             have r₂ := b2e22
             grind)
          | exact resolve b2e439 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e439
        have b2e446 : False := by grind
        exact b2e446
  · rcases eq_or_ne (M.op y x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op y x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b3e25 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b3e25
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
        have b3e28 : (k x y) = (τ (σ y)) := by
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
        have b3e29 : y = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e50 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e52 : x = y ∨ x = (k x y) := by grind
        clear b3e50
        have b3e53 : x = (k x y) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ (M.op y x) := by grind
          have b4e22 : y = (M.op y x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b4e47 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e112 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b4e119 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e120 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e478 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e119 (τ X1) (τ X0)
               have i₂ := b4e64 X1 X0
               grind)
            | exact superpose b4e64 b4e119
            | (have j0 := b4e119 (τ X1) (τ X0)
               grind)
            | exact resolve b4e119 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e489 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e478 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e478
            | (have j0 := b4e478 X0 X1
               grind)
            | exact resolve b4e478 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e478
          have b4e492 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e489 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e489
            | (have j0 := b4e489 X0 X1
               grind)
            | exact resolve b4e489 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e489
          have b4e494 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e492 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e492
            | (have j0 := b4e492 X0 X1
               grind)
            | exact resolve b4e492 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e492
          have b4e495 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e494 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e494
            | (have j0 := b4e494 X0 X1
               grind)
            | exact resolve b4e494 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e494
          have b4e496 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e495 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e495
            | (have j0 := b4e495 X0 X1
               grind)
            | exact resolve b4e495 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e495
          have b4e497 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e496 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e496
            | (have j0 := b4e496 X0 X1
               grind)
            | exact resolve b4e496 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e496
          have b4e522 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e120 (τ X1) (τ X0)
               have i₂ := b4e64 X1 X0
               grind)
            | exact superpose b4e64 b4e120
            | (have j0 := b4e120 (τ X1) (τ X0)
               grind)
            | exact resolve b4e120 b4e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e532 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e522 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e522
            | (have j0 := b4e522 X0 X1
               grind)
            | exact resolve b4e522 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e522
          have b4e535 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e532 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e532
            | (have j0 := b4e532 X0 X1
               grind)
            | exact resolve b4e532 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e532
          have b4e537 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e535 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e535
            | (have j0 := b4e535 X0 X1
               grind)
            | exact resolve b4e535 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e535
          have b4e538 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e537 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e537
            | (have j0 := b4e537 X0 X1
               grind)
            | exact resolve b4e537 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e537
          have b4e539 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e538 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e538
            | (have j0 := b4e538 X0 X1
               grind)
            | exact resolve b4e538 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e538
          have b4e540 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e539 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e539
            | (have j0 := b4e539 X0 X1
               grind)
            | exact resolve b4e539 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e539
          have b4e557 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e112
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e112
            | (have j1 := b4e18 (σ y) (σ x)
               grind)
            | exact resolve b4e112 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e112
          have b4e558 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e557
          have b4e4159 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e558
               grind)
            | exact superpose b4e558 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e558
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e558
               grind)
            | exact resolve b4e16 b4e558
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e558
          have b4e4161 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e4159
          have b4e4162 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e4161
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e4161
            | exact resolve b4e4161 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4161
          have b4e22026 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e4162
               grind)
            | exact superpose b4e4162 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e4162
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e4162
               grind)
            | exact resolve b4e17 b4e4162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e4162
          have b4e22028 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e22026
          have b4e22034 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e22028
               have r₂ := b4e25
               grind)
            | exact resolve b4e22028 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22028
          have b4e22036 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e22034
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e22034
            | exact resolve b4e22034 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22034
          have b4e22516 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e22036
               grind)
            | exact superpose b4e22036 b4e14
            | exact resolve b4e14 b4e22036
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22036
          have b4e22666 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e22516
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e22516
            | exact resolve b4e22516 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22516
          have b4e22668 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b4e540 y x
               grind)
            | (have r₁ := b4e22666
               have r₂ := b4e540 y x
               grind)
            | exact resolve b4e22666 b4e540
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e540 b4e22666
          have b4e22910 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e22668
               grind)
            | exact superpose b4e22668 b4e14
            | exact resolve b4e14 b4e22668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22668
          have b4e23060 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e22910
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e22910
            | exact resolve b4e22910 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e22910
          have b4e23061 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e497 y x
               grind)
            | (have r₁ := b4e23060
               have r₂ := b4e497 y x
               grind)
            | exact resolve b4e23060 b4e497
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e497 b4e23060
          have b4e23298 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e23061
               grind)
            | exact superpose b4e23061 b4e16
            | (have j0 := b4e16 y x
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e23061
               grind)
            | exact resolve b4e16 b4e23061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e23300 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e23298
          have b4e23485 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e119 x y
               have i₂ := b4e23300
               grind)
            | exact superpose b4e23300 b4e119
            | (have j0 := b4e119 x y
               grind)
            | exact resolve b4e119 b4e23300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119
          have b4e23530 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e23485
          have b4e29242 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e23530
               grind)
            | exact superpose b4e23530 b4e20
            | exact resolve b4e20 b4e23530
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23530
          have b4e29579 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e29242
               have i₂ := b4e23061
               grind)
            | exact superpose b4e23061 b4e29242
            | exact resolve b4e29242 b4e23061
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23061 b4e29242
          have b4e29582 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e29579
          have b4e29583 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e29582
               have r₂ := b4e26
               grind)
            | exact resolve b4e29582 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29582
          have b4e29936 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e29583
               grind)
            | exact superpose b4e29583 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e29583
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e29583
               grind)
            | exact resolve b4e17 b4e29583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29583
          have b4e29938 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e29936
          have b4e29944 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e29938
               have r₂ := b4e25
               grind)
            | exact resolve b4e29938 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29938
          have b4e29947 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e29944
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e29944
            | exact resolve b4e29944 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e29944
          have b4e30325 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e29947
               have i₂ := b4e23300
               grind)
            | exact superpose b4e23300 b4e29947
            | exact resolve b4e29947 b4e23300
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e23300 b4e29947
          have b4e30473 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e30325
          have b4e30531 : x = (M.op x y) := by
            first
            | (have r₁ := b4e30473
               have r₂ := b4e25
               grind)
            | exact resolve b4e30473 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30473
          have b4e30855 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e30531
               grind)
            | exact superpose b4e30531 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e30531
               grind)
            | exact resolve b4e17 b4e30531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e30857 : x = y ∨ y = (k y x) := by grind
          clear b4e30855
          have b4e30860 : y = (k y x) := by
            first
            | (have r₁ := b4e30857
               have r₂ := b4e26
               grind)
            | exact resolve b4e30857 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e30857
          have b4e31043 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e120 x y
               have i₂ := b4e30860
               grind)
            | exact superpose b4e30860 b4e120
            | (have j0 := b4e120 x y
               grind)
            | exact resolve b4e120 b4e30860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e120
          have b4e31069 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e31043
          have b4e35644 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e31069
               grind)
            | exact superpose b4e31069 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e31069
               grind)
            | exact resolve b4e16 b4e31069
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31069
          have b4e35646 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e35644
          have b4e35647 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e35646
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e35646
            | exact resolve b4e35646 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35646
          have b4e35650 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e35647
               have i₂ := b4e30860
               grind)
            | exact superpose b4e30860 b4e35647
            | exact resolve b4e35647 b4e30860
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30860 b4e35647
          have b4e35652 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e35650
               have r₂ := b4e25
               grind)
            | exact resolve b4e35650 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e35650
          have b4e36068 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e35652
               grind)
            | exact superpose b4e35652 b4e20
            | exact resolve b4e20 b4e35652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35652
          have b4e36080 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e36068
               have i₂ := b4e30531
               grind)
            | exact superpose b4e30531 b4e36068
            | exact resolve b4e36068 b4e30531
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30531 b4e36068
          have b4e36081 : False := by grind
          exact b4e36081
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op y x) := by grind
          have b5e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
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
          have b5e35 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e37 : x = y ∨ x = (k x y) := by grind
          clear b5e35
          have b5e38 : x = (k x y) := by
            first
            | (have r₁ := b5e37
               have r₂ := b5e25
               grind)
            | exact resolve b5e37 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e37
          have b5e41 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e113 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e41 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e433 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e113 y x
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e113
            | (have j0 := b5e113 y x
               grind)
            | exact resolve b5e113 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e113
          have b5e437 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e433
          have b5e440 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e437
               have r₂ := b5e24
               grind)
            | exact resolve b5e437 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e437
          have b5e444 : False := by grind
          exact b5e444
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op y x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ y) = (k (σ x) (σ y)) := by grind
        clear b6e23
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
        have b6e65 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
        have b6e67 : y = (M.op y x) ∨ x = (M.op y x) := by grind
        clear b6e65
        have b6e70 : x = (M.op y x) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
          have b7e35 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e37 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e35
          have b7e38 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e37
               have r₂ := b7e25
               grind)
            | exact resolve b7e37 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e37
          have b7e39 : (σ x) = (σ (k x y)) := by
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
          have b7e42 : (k x y) = (τ (σ x)) := by
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
          have b7e43 : x = (k x y) := by
            first
            | (have i₁ := b7e42
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e42
            | exact resolve b7e42 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e53 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
          have b7e54 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b7e53
          have b7e56 : y = (M.op y x) := by
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
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : y ≠ (M.op y x) := by grind
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e109 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e116 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e117 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e384 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e116 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e116
            | (have j0 := b8e116 (τ X1) (τ X0)
               grind)
            | exact resolve b8e116 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e391 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e394 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e391 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e391
            | (have j0 := b8e391 X0 X1
               grind)
            | exact resolve b8e391 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e391
          have b8e396 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e397 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e396 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e396
            | (have j0 := b8e396 X0 X1
               grind)
            | exact resolve b8e396 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e396
          have b8e398 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
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
          have b8e399 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e398
            | (have j0 := b8e398 X0 X1
               grind)
            | exact resolve b8e398 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e398
          have b8e448 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e117 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e117
            | (have j0 := b8e117 (τ X1) (τ X0)
               grind)
            | exact resolve b8e117 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e455 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e458 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e455 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e455
            | (have j0 := b8e455 X0 X1
               grind)
            | exact resolve b8e455 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e455
          have b8e460 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e461 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e460 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e460
            | (have j0 := b8e460 X0 X1
               grind)
            | exact resolve b8e460 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e460
          have b8e462 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
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
          have b8e463 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e462 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e462
            | (have j0 := b8e462 X0 X1
               grind)
            | exact resolve b8e462 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e462
          have b8e472 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e109
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e109
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e109 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e473 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e472
          have b8e3377 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e473
               grind)
            | exact superpose b8e473 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e473
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e473
               grind)
            | exact resolve b8e16 b8e473
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e473
          have b8e3379 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e3377
          have b8e3380 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3379
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3379
            | exact resolve b8e3379 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3379
          have b8e19943 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e3380
               grind)
            | exact superpose b8e3380 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e3380
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3380
               grind)
            | exact resolve b8e17 b8e3380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e19944 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3380
               grind)
            | exact superpose b8e3380 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3380
               grind)
            | exact resolve b8e16 b8e3380
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3380
          have b8e19945 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e19943
          have b8e19951 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e19944
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e19944
            | exact resolve b8e19944 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19944
          have b8e19952 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e19951
          have b8e19953 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e19945
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e19945
            | exact resolve b8e19945 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19945
          have b8e19956 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e19953
               have r₂ := b8e19952
               grind)
            | exact resolve b8e19953 b8e19952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19952 b8e19953
          have b8e20639 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e19956
               grind)
            | exact superpose b8e19956 b8e14
            | exact resolve b8e14 b8e19956
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e19956
          have b8e20787 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20639
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e20639
            | exact resolve b8e20639 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20639
          have b8e20790 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b8e463 y x
               grind)
            | (have r₁ := b8e20787
               have r₂ := b8e463 y x
               grind)
            | exact resolve b8e20787 b8e463
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463 b8e20787
          have b8e21034 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e20790
               grind)
            | exact superpose b8e20790 b8e14
            | exact resolve b8e14 b8e20790
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e20790
          have b8e21182 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e21034
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e21034
            | exact resolve b8e21034 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21034
          have b8e21183 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e399 y x
               grind)
            | (have r₁ := b8e21182
               have r₂ := b8e399 y x
               grind)
            | exact resolve b8e21182 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e21182
          have b8e21419 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e21183
               grind)
            | exact superpose b8e21183 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e21183
               grind)
            | exact resolve b8e16 b8e21183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21420 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e21421 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e21419
          have b8e21887 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e116 x y
               have i₂ := b8e21421
               grind)
            | exact superpose b8e21421 b8e116
            | (have j0 := b8e116 x y
               grind)
            | exact resolve b8e116 b8e21421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e21932 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e21887
          have b8e27268 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e21932
               grind)
            | exact superpose b8e21932 b8e20
            | exact resolve b8e20 b8e21932
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21932
          have b8e27963 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e27268
               have i₂ := b8e21183
               grind)
            | exact superpose b8e21183 b8e27268
            | exact resolve b8e27268 b8e21183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27268
          have b8e27966 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e27963
          have b8e27967 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e27966
               have r₂ := b8e21420
               grind)
            | exact resolve b8e27966 b8e21420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27966
          have b8e27994 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e27967
               grind)
            | exact superpose b8e27967 b8e20
            | exact resolve b8e20 b8e27967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e27998 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e27967
               grind)
            | exact superpose b8e27967 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e27967
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e27967
               grind)
            | exact resolve b8e17 b8e27967
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27967
          have b8e28000 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e27998
          have b8e28007 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e28000
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e28000
            | exact resolve b8e28000 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28000
          have b8e28329 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e27994
               have i₂ := b8e21183
               grind)
            | exact superpose b8e21183 b8e27994
            | exact resolve b8e27994 b8e21183
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21183 b8e27994
          have b8e28333 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e28329
               have r₂ := b8e21420
               grind)
            | exact resolve b8e28329 b8e21420
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21420 b8e28329
          have b8e29489 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e28007
               have i₂ := b8e21421
               grind)
            | exact superpose b8e21421 b8e28007
            | exact resolve b8e28007 b8e21421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21421 b8e28007
          have b8e29626 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e29489
          have b8e29742 : x = (M.op x y) := by
            first
            | (have r₁ := b8e29626
               have r₂ := b8e28333
               grind)
            | exact resolve b8e29626 b8e28333
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e28333 b8e29626
          have b8e29864 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e29742
               grind)
            | exact superpose b8e29742 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e29742
               grind)
            | exact resolve b8e17 b8e29742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29865 : x ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e29742
               grind)
            | exact superpose b8e29742 b8e16
            | (have j0 := b8e16 y x
               grind)
            | exact resolve b8e16 b8e29742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e29866 : y = (k y x) ∨ x = y := by grind
          clear b8e29864
          have b8e30695 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e117 x y
               have i₂ := b8e29866
               grind)
            | exact superpose b8e29866 b8e117
            | (have j0 := b8e117 x y
               grind)
            | exact resolve b8e117 b8e29866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e117
          have b8e30721 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e30695
          have b8e34117 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e30721
               grind)
            | exact superpose b8e30721 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e30721
               grind)
            | exact resolve b8e16 b8e30721
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30721
          have b8e34119 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e34117
          have b8e34120 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e34119
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e34119
            | exact resolve b8e34119 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34119
          have b8e34853 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e34120
               grind)
            | exact superpose b8e34120 b8e20
            | exact resolve b8e20 b8e34120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34120
          have b8e34869 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e34853
               have i₂ := b8e29742
               grind)
            | exact superpose b8e29742 b8e34853
            | exact resolve b8e34853 b8e29742
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34853
          have b8e34870 : (σ x) = (σ (k y x)) ∨ x = y := by grind
          clear b8e34869
          have b8e35277 : (k y x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e34870
               grind)
            | exact superpose b8e34870 b8e14
            | exact resolve b8e14 b8e34870
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34870
          have b8e35486 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e35277
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e35277
            | exact resolve b8e35277 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35277
          have b8e35487 : x = (k y x) := by
            first
            | (have r₁ := b8e35486
               have r₂ := b8e29865
               grind)
            | exact resolve b8e35486 b8e29865
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29865 b8e35486
          have b8e35835 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e29866
               have i₂ := b8e35487
               grind)
            | exact superpose b8e35487 b8e29866
            | exact resolve b8e29866 b8e35487
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29866 b8e35487
          have b8e35866 : x = y := by grind
          clear b8e35835
          have b8e36281 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e35866
               grind)
            | exact superpose b8e35866 b8e22
            | exact resolve b8e22 b8e35866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36316 : x = (M.op x x) := by
            first
            | (have i₁ := b8e29742
               have i₂ := b8e35866
               grind)
            | exact superpose b8e35866 b8e29742
            | exact resolve b8e29742 b8e35866
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e29742 b8e35866
          have b8e36352 : False := by grind
          exact b8e36352
