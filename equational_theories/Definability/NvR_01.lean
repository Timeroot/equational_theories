import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1286`: `x = y ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1286 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1286 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1286.models_iff G M).mp hM
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
        have b1e44 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e46 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e44
        have b1e47 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e46
             have r₂ := b1e23
             grind)
          | exact resolve b1e46 b1e23
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
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e48
          | exact resolve b1e48 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e48
        have b1e50 : False := by grind
        exact b1e50
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
        have b2e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e128 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e48 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e514 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e128 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e128
          | (have j0 := b2e128 x y
             grind)
          | exact resolve b2e128 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e128
        have b2e517 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e514
        have b2e520 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e517
             have r₂ := b2e22
             grind)
          | exact resolve b2e517 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e517
        have b2e524 : False := by grind
        exact b2e524
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
        have b3e42 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e44 : x = y ∨ y = (k x y) := by grind
        clear b3e42
        have b3e45 : y = (k x y) := by
          first
          | (have r₁ := b3e44
             have r₂ := b3e23
             grind)
          | exact resolve b3e44 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e44
        have b3e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e45
             grind)
          | exact superpose b3e45 b3e29
          | exact resolve b3e29 b3e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e45
        have b3e49 : False := by grind
        exact b3e49
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
          have b5e40 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          clear b5e40
          have b5e44 : y = (k x y) := by
            first
            | (have r₁ := b5e43
               have r₂ := b5e25
               grind)
            | exact resolve b5e43 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e43
          have b5e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e115 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e474 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e115 x y
               have i₂ := b5e44
               grind)
            | exact superpose b5e44 b5e115
            | (have j0 := b5e115 x y
               grind)
            | exact resolve b5e115 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e115
          have b5e477 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e474
          have b5e480 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e477
               have r₂ := b5e24
               grind)
            | exact resolve b5e477 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e477
          have b5e484 : False := by grind
          exact b5e484
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
        have b6e47 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e49 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e47
        have b6e52 : y = (M.op x y) := by
          first
          | (have r₁ := b6e49
             have r₂ := b6e21
             grind)
          | exact resolve b6e49 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49
        have b6e55 : False := by grind
        exact b6e55
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
          have b7e37 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e25
               grind)
            | exact resolve b7e39 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e39
          have b7e41 : (σ y) = (σ (k x y)) := by
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
          have b7e44 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e41
               grind)
            | exact superpose b7e41 b7e14
            | exact resolve b7e14 b7e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e41
          have b7e45 : y = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e45
               grind)
            | exact superpose b7e45 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e56 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e55
          have b7e58 : x = (M.op x y) := by
            first
            | (have r₁ := b7e56
               have r₂ := b7e21
               grind)
            | exact resolve b7e56 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e56
          have b7e60 : False := by grind
          exact b7e60
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
          have b8e97 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e107 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e97
               have r₂ := b8e24
               grind)
            | exact resolve b8e97 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e110 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e107
               have r₂ := b8e23
               grind)
            | exact resolve b8e107 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e107
          have b8e111 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e110
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e110
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e110 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e112 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e111
          have b8e113 : y = (M.op x y) := by
            first
            | (have r₁ := b8e112
               have r₂ := b8e22
               grind)
            | exact resolve b8e112 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e114 : False := by grind
          exact b8e114

/-- `Equation1286`: `x = y ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1286 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1286 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1286.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X0 X1) X0) X1)) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
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
      have b0e19 : x = (M.op y x) := by grind
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
      have b0e32 : y = (M.op x (M.op (M.op x y) x)) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x))) := by
        first
        | (have i₁ := b0e11 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : x = (M.op (M.op (M.op x y) x) (M.op (M.op y x) (M.op (M.op x y) x))) := by
        first
        | (have i₁ := b0e11 x (M.op (M.op x y) x)
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : x = (M.op (M.op (M.op x y) x) (M.op x (M.op (M.op x y) x))) := by
        first
        | (have i₁ := b0e36
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e36
        | exact resolve b0e36 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e39 : x = (M.op (M.op (M.op x y) x) y) := by
        first
        | (have i₁ := b0e38
           have i₂ := b0e32
           grind)
        | exact superpose b0e32 b0e38
        | exact resolve b0e38 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32 b0e38
      have b0e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
      have b0e64 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (M.op (σ y) (σ x)) (M.op (M.op (σ x) (σ y)) (σ x)))) := by
        first
        | (have i₁ := b0e11 (σ x) (M.op (M.op (σ x) (σ y)) (σ x))
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e11
        | exact resolve b0e11 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (σ x)))) := by
        first
        | (have i₁ := b0e64
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e64
        | exact resolve b0e64 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e67 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e66
           have i₂ := b0e33
           grind)
        | exact superpose b0e33 b0e66
        | exact resolve b0e66 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33 b0e66
      have b0e68 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e152 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e49 x y
           grind)
        | exact superpose b0e49 b0e18
        | (have j1 := b0e49 x y
           grind)
        | exact resolve b0e18 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e159 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e49 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49
      have b0e618 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e159 (τ X1) (τ X0)
           have i₂ := b0e68 X1 X0
           grind)
        | exact superpose b0e68 b0e159
        | (have j0 := b0e159 (τ X1) (τ X0)
           grind)
        | exact resolve b0e159 b0e68
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e626 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e618 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e618
        | (have j0 := b0e618 X0 X1
           grind)
        | exact resolve b0e618 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e618
      have b0e629 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e626 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e626
        | (have j0 := b0e626 X0 X1
           grind)
        | exact resolve b0e626 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e626
      have b0e631 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e629 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e629
        | (have j0 := b0e629 X0 X1
           grind)
        | exact resolve b0e629 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e629
      have b0e632 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e631 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e631
        | (have j0 := b0e631 X0 X1
           grind)
        | exact resolve b0e631 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e631
      have b0e633 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e632 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e632
        | (have j0 := b0e632 X0 X1
           grind)
        | exact resolve b0e632 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e632
      have b0e634 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e633 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e633
        | (have j0 := b0e633 X0 X1
           grind)
        | exact resolve b0e633 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e633
      have b0e646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e152
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e152
        | (have j1 := b0e16 (σ y) (σ x)
           grind)
        | exact resolve b0e152 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e152
      have b0e647 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e646
      have b0e4559 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e67
           have i₂ := b0e647
           grind)
        | exact superpose b0e647 b0e67
        | exact resolve b0e67 b0e647
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e647
      have b0e4584 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4559
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e4559
        | exact resolve b0e4559 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4559
      have b0e4585 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e4584
      have b0e4602 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e4585
           grind)
        | exact superpose b0e4585 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e4585
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e4585
           grind)
        | exact resolve b0e15 b0e4585
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4585
      have b0e4610 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e4602
      have b0e4612 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4610
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e4610
        | exact resolve b0e4610 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4610
      have b0e7775 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e4612
           grind)
        | exact superpose b0e4612 b0e12
        | exact resolve b0e12 b0e4612
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4612
      have b0e7836 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e7775
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e7775
        | exact resolve b0e7775 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7775
      have b0e7837 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have j1 := b0e634 y x
           grind)
        | (have r₁ := b0e7836
           have r₂ := b0e634 y x
           grind)
        | exact resolve b0e7836 b0e634
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e634 b0e7836
      have b0e7842 : x = (M.op (M.op y x) y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e39
           have i₂ := b0e7837
           grind)
        | exact superpose b0e7837 b0e39
        | exact resolve b0e39 b0e7837
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39 b0e7837
      have b0e7870 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e7842
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e7842
        | exact resolve b0e7842 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7842
      have b0e7871 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
      clear b0e7870
      have b0e8043 : x ≠ x ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e15 y x
           have i₂ := b0e7871
           grind)
        | exact superpose b0e7871 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e7871
           grind)
        | exact resolve b0e15 b0e7871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8051 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e8043
      have b0e8672 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e159 x y
           have i₂ := b0e8051
           grind)
        | exact superpose b0e8051 b0e159
        | (have j0 := b0e159 x y
           grind)
        | exact resolve b0e159 b0e8051
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e159 b0e8051
      have b0e8682 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e8672
      have b0e30841 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e67
           have i₂ := b0e8682
           grind)
        | exact superpose b0e8682 b0e67
        | exact resolve b0e67 b0e8682
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67 b0e8682
      have b0e30877 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e30841
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e30841
        | exact resolve b0e30841 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30841
      have b0e30878 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e30877
      have b0e31233 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e30878
           grind)
        | exact superpose b0e30878 b0e18
        | exact resolve b0e18 b0e30878
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30878
      have b0e31587 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e31233
           have i₂ := b0e7871
           grind)
        | exact superpose b0e7871 b0e31233
        | exact resolve b0e31233 b0e7871
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7871 b0e31233
      have b0e31592 : (σ x) ≠ (σ x) ∨ x = y ∨ (σ x) = (σ y) := by grind
      clear b0e31587
      have b0e31593 : (σ x) = (σ y) ∨ x = y := by grind
      clear b0e31592
      have b0e31968 : y = (τ (σ x)) ∨ x = y := by
        first
        | (have i₁ := b0e12 y
           have i₂ := b0e31593
           grind)
        | exact superpose b0e31593 b0e12
        | exact resolve b0e12 b0e31593
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31593
      have b0e32122 : x = y ∨ x = y := by
        first
        | (have i₁ := b0e31968
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e31968
        | exact resolve b0e31968 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31968
      have b0e32123 : x = y := by grind
      clear b0e32122
      have b0e32448 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e32123
           grind)
        | exact superpose b0e32123 b0e18
        | exact resolve b0e18 b0e32123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32449 : x = (M.op x x) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e32123
           grind)
        | exact superpose b0e32123 b0e19
        | exact resolve b0e19 b0e32123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32450 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e32123
           grind)
        | exact superpose b0e32123 b0e20
        | exact resolve b0e20 b0e32123
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32123
      have b0e32568 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e32448
           have i₂ := b0e32449
           grind)
        | exact superpose b0e32449 b0e32448
        | exact resolve b0e32448 b0e32449
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32448 b0e32449
      have b0e32576 : False := by grind
      exact b0e32576
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
        have b1e38 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e40 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e38
        have b1e41 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e40
             have r₂ := b1e23
             grind)
          | exact resolve b1e40 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e41
          | exact resolve b1e41 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e43 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e42
          | exact resolve b1e42 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e42
        have b1e44 : False := by grind
        exact b1e44
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
        have b2e44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e140 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e44 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e514 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e140 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e140
          | (have j0 := b2e140 y x
             grind)
          | exact resolve b2e140 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e140
        have b2e517 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e514
        have b2e520 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e517
             have r₂ := b2e22
             grind)
          | exact resolve b2e517 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e517
        have b2e524 : False := by grind
        exact b2e524
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
        have b3e49 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e50 : x = y ∨ x = (k x y) := by grind
        clear b3e49
        have b3e51 : x = (k x y) := by
          first
          | (have r₁ := b3e50
             have r₂ := b3e23
             grind)
          | exact resolve b3e50 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e53 : x = y := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e51
             grind)
          | exact superpose b3e51 b3e29
          | exact resolve b3e29 b3e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e51
        have b3e55 : False := by grind
        exact b3e55
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
          have b4e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e54 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e29 X1 X0
               have i₂ := b4e18 (τ X1) X0
               grind)
            | exact superpose b4e18 b4e29
            | (have j1 := b4e18 (τ X1) X0
               grind)
            | exact resolve b4e29 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e57 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e67 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e57 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e57
            | exact resolve b4e57 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e57
          have b4e147 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e49 x y
               grind)
            | exact superpose b4e49 b4e20
            | (have j1 := b4e49 x y
               grind)
            | exact resolve b4e20 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e153 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e154 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e315 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e54 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e54
            | exact resolve b4e54 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e344 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e315 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e315
            | (have j0 := b4e315 X0 X1
               grind)
            | exact resolve b4e315 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e315
          have b4e591 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e153 (τ X1) (τ X0)
               have i₂ := b4e67 X1 X0
               grind)
            | exact superpose b4e67 b4e153
            | (have j0 := b4e153 (τ X1) (τ X0)
               grind)
            | exact resolve b4e153 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e602 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e591 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e591
            | (have j0 := b4e591 X0 X1
               grind)
            | exact resolve b4e591 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e591
          have b4e606 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e602 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e602
            | (have j0 := b4e602 X0 X1
               grind)
            | exact resolve b4e602 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e602
          have b4e609 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e606 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e606
            | (have j0 := b4e606 X0 X1
               grind)
            | exact resolve b4e606 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e606
          have b4e611 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e609 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e609
            | (have j0 := b4e609 X0 X1
               grind)
            | exact resolve b4e609 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e609
          have b4e613 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e611 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e611
            | (have j0 := b4e611 X0 X1
               grind)
            | exact resolve b4e611 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e611
          have b4e614 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e613 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e613
            | (have j0 := b4e613 X0 X1
               grind)
            | exact resolve b4e613 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e613
          have b4e628 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e154 (τ X1) (τ X0)
               have i₂ := b4e67 X1 X0
               grind)
            | exact superpose b4e67 b4e154
            | (have j0 := b4e154 (τ X1) (τ X0)
               grind)
            | exact resolve b4e154 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67
          have b4e640 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e628 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e628
            | (have j0 := b4e628 X0 X1
               grind)
            | exact resolve b4e628 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e628
          have b4e644 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e640 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e640
            | (have j0 := b4e640 X0 X1
               grind)
            | exact resolve b4e640 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e640
          have b4e647 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e644 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e644
            | (have j0 := b4e644 X0 X1
               grind)
            | exact resolve b4e644 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e644
          have b4e649 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e647 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e647
            | (have j0 := b4e647 X0 X1
               grind)
            | exact resolve b4e647 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e647
          have b4e651 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e649 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e649
            | (have j0 := b4e649 X0 X1
               grind)
            | exact resolve b4e649 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e649
          have b4e652 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e651 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e651
            | (have j0 := b4e651 X0 X1
               grind)
            | exact resolve b4e651 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e651
          have b4e678 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e147
               have i₂ := b4e344 y x
               grind)
            | exact superpose b4e344 b4e147
            | (have j1 := b4e344 (σ y) (σ x)
               grind)
            | (have r₁ := b4e147
               have r₂ := b4e344 y x
               grind)
            | exact resolve b4e147 b4e344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e147 b4e344
          have b4e679 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e678
          have b4e48872 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e679
               grind)
            | exact superpose b4e679 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e679
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e679
               grind)
            | exact resolve b4e16 b4e679
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e679
          have b4e48883 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e48872
          have b4e48893 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e48883
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e48883
            | exact resolve b4e48883 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48883
          have b4e49455 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e48893
               grind)
            | exact superpose b4e48893 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e48893
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e48893
               grind)
            | exact resolve b4e17 b4e48893
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48893
          have b4e49465 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e49455
          have b4e49470 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e49465
               have r₂ := b4e25
               grind)
            | exact resolve b4e49465 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49465
          have b4e49471 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e49470
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e49470
            | exact resolve b4e49470 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49470
          have b4e50558 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e49471
               grind)
            | exact superpose b4e49471 b4e14
            | exact resolve b4e14 b4e49471
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49471
          have b4e50781 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e50558
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e50558
            | exact resolve b4e50558 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50558
          have b4e50782 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b4e652 y x
               grind)
            | (have r₁ := b4e50781
               have r₂ := b4e652 y x
               grind)
            | exact resolve b4e50781 b4e652
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e652 b4e50781
          have b4e51245 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e50782
               grind)
            | exact superpose b4e50782 b4e14
            | exact resolve b4e14 b4e50782
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50782
          have b4e51471 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e51245
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e51245
            | exact resolve b4e51245 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51245
          have b4e51472 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e614 y x
               grind)
            | (have r₁ := b4e51471
               have r₂ := b4e614 y x
               grind)
            | exact resolve b4e51471 b4e614
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e614 b4e51471
          have b4e51984 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e51472
               grind)
            | exact superpose b4e51472 b4e16
            | (have j0 := b4e16 y x
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e51472
               grind)
            | exact resolve b4e16 b4e51472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51995 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e51984
          have b4e52474 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e153 x y
               have i₂ := b4e51995
               grind)
            | exact superpose b4e51995 b4e153
            | (have j0 := b4e153 x y
               grind)
            | exact resolve b4e153 b4e51995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e153
          have b4e52547 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e52474
          have b4e67683 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e52547
               grind)
            | exact superpose b4e52547 b4e20
            | exact resolve b4e20 b4e52547
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52547
          have b4e68289 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e67683
               have i₂ := b4e51472
               grind)
            | exact superpose b4e51472 b4e67683
            | exact resolve b4e67683 b4e51472
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51472 b4e67683
          have b4e68292 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e68289
          have b4e68293 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e68292
               have r₂ := b4e26
               grind)
            | exact resolve b4e68292 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68292
          have b4e68803 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e68293
               grind)
            | exact superpose b4e68293 b4e17
            | (have j0 := b4e17 (σ y) (σ x)
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e68293
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e68293
               grind)
            | exact resolve b4e17 b4e68293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68293
          have b4e68813 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b4e68803
          have b4e68818 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e68813
               have r₂ := b4e25
               grind)
            | exact resolve b4e68813 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68813
          have b4e68819 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e68818
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e68818
            | exact resolve b4e68818 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68818
          have b4e69883 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e68819
               have i₂ := b4e51995
               grind)
            | exact superpose b4e51995 b4e68819
            | exact resolve b4e68819 b4e51995
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51995 b4e68819
          have b4e70160 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b4e69883
          have b4e70218 : x = (M.op x y) := by
            first
            | (have r₁ := b4e70160
               have r₂ := b4e25
               grind)
            | exact resolve b4e70160 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70160
          have b4e70796 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e70218
               grind)
            | exact superpose b4e70218 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e70218
               grind)
            | exact resolve b4e17 b4e70218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70806 : x = y ∨ y = (k y x) := by grind
          clear b4e70796
          have b4e70809 : y = (k y x) := by
            first
            | (have r₁ := b4e70806
               have r₂ := b4e26
               grind)
            | exact resolve b4e70806 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e70806
          have b4e71325 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e154 x y
               have i₂ := b4e70809
               grind)
            | exact superpose b4e70809 b4e154
            | (have j0 := b4e154 x y
               grind)
            | exact resolve b4e154 b4e70809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e154
          have b4e71366 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e71325
          have b4e78484 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e71366
               grind)
            | exact superpose b4e71366 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e71366
               grind)
            | exact resolve b4e16 b4e71366
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71366
          have b4e78496 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e78484
          have b4e78507 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e78496
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e78496
            | exact resolve b4e78496 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78496
          have b4e78516 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e78507
               have i₂ := b4e70809
               grind)
            | exact superpose b4e70809 b4e78507
            | exact resolve b4e78507 b4e70809
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70809 b4e78507
          have b4e78520 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e78516
               have r₂ := b4e25
               grind)
            | exact resolve b4e78516 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e78516
          have b4e79269 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e78520
               grind)
            | exact superpose b4e78520 b4e20
            | exact resolve b4e20 b4e78520
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78520
          have b4e79287 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e79269
               have i₂ := b4e70218
               grind)
            | exact superpose b4e70218 b4e79269
            | exact resolve b4e79269 b4e70218
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70218 b4e79269
          have b4e79288 : False := by grind
          exact b4e79288
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
          have b5e38 : x = y ∨ x = (k x y) := by grind
          clear b5e35
          have b5e39 : x = (k x y) := by
            first
            | (have r₁ := b5e38
               have r₂ := b5e25
               grind)
            | exact resolve b5e38 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e38
          have b5e42 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e127 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e42 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e42
          have b5e523 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e127 y x
               have i₂ := b5e39
               grind)
            | exact superpose b5e39 b5e127
            | (have j0 := b5e127 y x
               grind)
            | exact resolve b5e127 b5e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e39 b5e127
          have b5e527 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e523
          have b5e530 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e527
               have r₂ := b5e24
               grind)
            | exact resolve b5e527 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e527
          have b5e534 : False := by grind
          exact b5e534
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
        have b6e66 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
        have b6e68 : y = (M.op y x) ∨ x = (M.op y x) := by grind
        clear b6e66
        have b6e71 : x = (M.op y x) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e21
             grind)
          | exact resolve b6e68 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e74 : False := by grind
        exact b6e74
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
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e25
               grind)
            | exact resolve b7e38 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e38
          have b7e40 : (σ x) = (σ (k x y)) := by
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
          have b7e43 : (k x y) = (τ (σ x)) := by
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
          have b7e44 : x = (k x y) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e43
            | exact resolve b7e43 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : x = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
          have b7e55 : x = (M.op y x) ∨ y = (M.op y x) := by grind
          clear b7e54
          have b7e57 : y = (M.op y x) := by
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
          have b8e99 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e105 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e106 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e325 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e105 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e105
            | (have j0 := b8e105 (τ X1) (τ X0)
               grind)
            | exact resolve b8e105 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e332 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e325 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e325
            | (have j0 := b8e325 X0 X1
               grind)
            | exact resolve b8e325 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e325
          have b8e335 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e332 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e332
            | (have j0 := b8e332 X0 X1
               grind)
            | exact resolve b8e332 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e332
          have b8e337 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e335 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e335
            | (have j0 := b8e335 X0 X1
               grind)
            | exact resolve b8e335 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e335
          have b8e338 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e337 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e337
            | (have j0 := b8e337 X0 X1
               grind)
            | exact resolve b8e337 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e337
          have b8e339 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e338 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e338
            | (have j0 := b8e338 X0 X1
               grind)
            | exact resolve b8e338 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338
          have b8e340 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e339 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e339
            | (have j0 := b8e339 X0 X1
               grind)
            | exact resolve b8e339 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339
          have b8e385 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e106 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e106
            | (have j0 := b8e106 (τ X1) (τ X0)
               grind)
            | exact resolve b8e106 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e392 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e385 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e385
            | (have j0 := b8e385 X0 X1
               grind)
            | exact resolve b8e385 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e385
          have b8e395 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e392 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e392
            | (have j0 := b8e392 X0 X1
               grind)
            | exact resolve b8e392 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e392
          have b8e397 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e395 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e395
            | (have j0 := b8e395 X0 X1
               grind)
            | exact resolve b8e395 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e395
          have b8e398 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e397 X0 X0
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
          have b8e399 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X1
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
          have b8e400 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e399 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e399
            | (have j0 := b8e399 X0 X1
               grind)
            | exact resolve b8e399 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399
          have b8e445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e99
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e99
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e99 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e99
          have b8e446 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e445
          have b8e3679 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e446
               grind)
            | exact superpose b8e446 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e446
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e446
               grind)
            | exact resolve b8e16 b8e446
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e446
          have b8e3688 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e3679
          have b8e3689 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3688
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3688
            | exact resolve b8e3688 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3688
          have b8e21115 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3689
               grind)
            | exact superpose b8e3689 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3689
               grind)
            | exact resolve b8e16 b8e3689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21116 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e3689
               grind)
            | exact superpose b8e3689 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e3689
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3689
               grind)
            | exact resolve b8e17 b8e3689
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3689
          have b8e21125 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e21116
          have b8e21128 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e21125
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e21125
            | exact resolve b8e21125 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21125
          have b8e21129 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e21115
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e21115
            | exact resolve b8e21115 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21115
          have b8e21130 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e21129
          have b8e145892 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e21128
               grind)
            | exact superpose b8e21128 b8e14
            | exact resolve b8e14 b8e21128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21128
          have b8e145933 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e145892
               have r₂ := b8e21130
               grind)
            | exact resolve b8e145892 b8e21130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21130 b8e145892
          have b8e145951 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e145933
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e145933
            | exact resolve b8e145933 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145933
          have b8e145952 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b8e400 y x
               grind)
            | (have r₁ := b8e145951
               have r₂ := b8e400 y x
               grind)
            | exact resolve b8e145951 b8e400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e400 b8e145951
          have b8e146188 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e145952
               grind)
            | exact superpose b8e145952 b8e14
            | exact resolve b8e14 b8e145952
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145952
          have b8e146363 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e146188
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e146188
            | exact resolve b8e146188 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146188
          have b8e146364 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e340 y x
               grind)
            | (have r₁ := b8e146363
               have r₂ := b8e340 y x
               grind)
            | exact resolve b8e146363 b8e340
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e340 b8e146363
          have b8e146594 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e146364
               grind)
            | exact superpose b8e146364 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e146364
               grind)
            | exact resolve b8e16 b8e146364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e146608 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e146609 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b8e146594
          have b8e147066 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e105 x y
               have i₂ := b8e146609
               grind)
            | exact superpose b8e146609 b8e105
            | (have j0 := b8e105 x y
               grind)
            | exact resolve b8e105 b8e146609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e147273 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b8e147066
          have b8e151831 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e147273
               grind)
            | exact superpose b8e147273 b8e20
            | exact resolve b8e20 b8e147273
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e147273
          have b8e152360 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e151831
               have i₂ := b8e146364
               grind)
            | exact superpose b8e146364 b8e151831
            | exact resolve b8e151831 b8e146364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e151831
          have b8e152363 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b8e152360
          have b8e152364 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e152363
               have r₂ := b8e146608
               grind)
            | exact resolve b8e152363 b8e146608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152363
          have b8e152662 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e152364
               grind)
            | exact superpose b8e152364 b8e20
            | exact resolve b8e20 b8e152364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e152665 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e152364
               grind)
            | exact superpose b8e152364 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e152364
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e152364
               grind)
            | exact resolve b8e17 b8e152364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152364
          have b8e152677 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e152665
          have b8e152680 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e152677
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e152677
            | exact resolve b8e152677 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152677
          have b8e152966 : (σ x) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e152662
               have i₂ := b8e146364
               grind)
            | exact superpose b8e146364 b8e152662
            | exact resolve b8e152662 b8e146364
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146364 b8e152662
          have b8e152970 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e152966
               have r₂ := b8e146608
               grind)
            | exact resolve b8e152966 b8e146608
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146608 b8e152966
          have b8e153543 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e152680
               have i₂ := b8e146609
               grind)
            | exact superpose b8e146609 b8e152680
            | exact resolve b8e152680 b8e146609
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e146609 b8e152680
          have b8e153691 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e153543
          have b8e153789 : x = (M.op x y) := by
            first
            | (have r₁ := b8e153691
               have r₂ := b8e152970
               grind)
            | exact resolve b8e153691 b8e152970
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152970 b8e153691
          have b8e154138 : x ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e153789
               grind)
            | exact superpose b8e153789 b8e16
            | (have j0 := b8e16 y x
               grind)
            | exact resolve b8e16 b8e153789
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e154139 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e153789
               grind)
            | exact superpose b8e153789 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e153789
               grind)
            | exact resolve b8e17 b8e153789
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e154154 : y = (k y x) ∨ x = y := by grind
          clear b8e154139
          have b8e154735 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e106 x y
               have i₂ := b8e154154
               grind)
            | exact superpose b8e154154 b8e106
            | (have j0 := b8e106 x y
               grind)
            | exact resolve b8e106 b8e154154
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e106
          have b8e154842 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e154735
          have b8e157008 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e154842
               grind)
            | exact superpose b8e154842 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e154842
               grind)
            | exact resolve b8e16 b8e154842
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154842
          have b8e157014 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e157008
          have b8e157017 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e157014
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e157014
            | exact resolve b8e157014 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157014
          have b8e157613 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e157017
               grind)
            | exact superpose b8e157017 b8e20
            | exact resolve b8e20 b8e157017
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157017
          have b8e157627 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e157613
               have i₂ := b8e153789
               grind)
            | exact superpose b8e153789 b8e157613
            | exact resolve b8e157613 b8e153789
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157613
          have b8e157628 : (σ x) = (σ (k y x)) ∨ x = y := by grind
          clear b8e157627
          have b8e157950 : (k y x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e157628
               grind)
            | exact superpose b8e157628 b8e14
            | exact resolve b8e14 b8e157628
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157628
          have b8e158123 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e157950
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e157950
            | exact resolve b8e157950 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e157950
          have b8e158124 : x = (k y x) := by
            first
            | (have r₁ := b8e158123
               have r₂ := b8e154138
               grind)
            | exact resolve b8e158123 b8e154138
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154138 b8e158123
          have b8e158418 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e154154
               have i₂ := b8e158124
               grind)
            | exact superpose b8e158124 b8e154154
            | exact resolve b8e154154 b8e158124
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e154154 b8e158124
          have b8e158534 : x = y := by grind
          clear b8e158418
          have b8e158815 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e158534
               grind)
            | exact superpose b8e158534 b8e22
            | exact resolve b8e22 b8e158534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e158853 : x = (M.op x x) := by
            first
            | (have i₁ := b8e153789
               have i₂ := b8e158534
               grind)
            | exact superpose b8e158534 b8e153789
            | exact resolve b8e153789 b8e158534
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153789 b8e158534
          have b8e158887 : False := by grind
          exact b8e158887

/-- `Equation1323`: `x = y ◇ (((y ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1323 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1323 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1323.models_iff G M).mp hM
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
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
      have b0e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e47 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e17 X0 X0
           have i₂ := b0e41 (σ X0)
           grind)
        | exact superpose b0e41 b0e17
        | exact resolve b0e17 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e52 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e47 X0
           have i₂ := b0e41 X0
           grind)
        | exact superpose b0e41 b0e47
        | exact resolve b0e47 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e47
      have b0e185 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e52 x
           grind)
        | exact superpose b0e52 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e52 x
           grind)
        | exact resolve b0e22 b0e52
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e52
      have b0e198 : False := by grind
      exact b0e198
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
          intro X0 X1
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e26 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
             have i₂ := b1e12 X0 (M.op X1 X1)
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e51 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
        clear b1e51
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
        have b1e213 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X1 (M.op X0 X0)
             have i₂ := b1e26 X1 X0
             grind)
          | exact superpose b1e26 b1e12
          | exact resolve b1e12 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e453 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ (M.op y y)))) := by
          first
          | (have i₁ := b1e213 (σ y) (σ x)
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e213
          | exact resolve b1e213 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e454 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
          intro X0
          first
          | (have i₁ := b1e213 (σ X0) (σ X0)
             have i₂ := b1e65 X0
             grind)
          | exact superpose b1e65 b1e213
          | exact resolve b1e213 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65 b1e213
        have b1e464 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op y y)))) := by
          first
          | (have i₁ := b1e453
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e453
          | exact resolve b1e453 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e453
        have b1e469 : (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (σ (M.op y y)))) := by
          first
          | (have i₁ := b1e464
             have i₂ := b1e56
             grind)
          | exact superpose b1e56 b1e464
          | exact resolve b1e464 b1e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56 b1e464
        have b1e470 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e469
             have i₂ := b1e454 y
             grind)
          | exact superpose b1e454 b1e469
          | exact resolve b1e469 b1e454
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e454 b1e469
        have b1e597 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e470
             grind)
          | exact superpose b1e470 b1e21
          | exact resolve b1e21 b1e470
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e470
        have b1e608 : False := by grind
        exact b1e608
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b2e49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e50 : (M.op y y) = (k x y) := by grind
        clear b2e47
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
        have b2e85 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e156 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
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
        have b2e815 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e85 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e85
        have b2e816 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e815
             have r₂ := b2e21
             grind)
          | exact resolve b2e815 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e815
        have b2e818 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e816
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e816
          | exact resolve b2e816 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e816
        have b2e820 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e818
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e818
          | exact resolve b2e818 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e818
        have b2e822 : False := by grind
        exact b2e822
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b3e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e53 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e51
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
        have b3e71 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e77 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
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
             have i₂ := b3e52 y
             grind)
          | exact superpose b3e52 b3e78
          | exact resolve b3e78 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e78
        have b3e80 : (σ (M.op x y)) = (σ (k x y)) := by
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
        have b3e208 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
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
        have b3e223 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e71 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e224 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e223
             have r₂ := b3e20
             grind)
          | exact resolve b3e223 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e223
        have b3e228 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e224
             grind)
          | exact superpose b3e224 b3e80
          | exact resolve b3e80 b3e224
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80 b3e224
        have b3e232 : False := by grind
        exact b3e232
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
          have b4e67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e68 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e66
          have b4e70 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e68
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e68
            | exact resolve b4e68 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e72 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e67 y
               grind)
            | exact superpose b4e67 b4e70
            | exact resolve b4e70 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e70
          have b4e73 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e72
            | exact resolve b4e72 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e72
          have b4e74 : False := by grind
          exact b4e74
        · have b5e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
            intro X0 X1
            grind
          have b5e22 : (M.op x y) = (M.op y y) := by grind
          have b5e24 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
               have i₂ := b5e13 X0 (M.op X1 X1)
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e228 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0)
               have i₂ := b5e32 X1 X0
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e244 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op X0 y))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e228 y X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e228
            | exact resolve b5e228 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e254 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
            first
            | (have i₁ := b5e228 y y
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e228
            | exact resolve b5e228 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e228
          have b5e298 : x = y := by
            first
            | (have i₁ := b5e244 x
               have i₂ := b5e254
               grind)
            | exact superpose b5e254 b5e244
            | exact resolve b5e244 b5e254
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e244 b5e254
          have b5e401 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e298
               grind)
            | exact superpose b5e298 b5e24
            | exact resolve b5e24 b5e298
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e298
          have b5e408 : False := by grind
          exact b5e408
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : (M.op x y) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e48 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e50 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
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
        have b6e71 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e70
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
             have i₂ := b6e49 y
             grind)
          | exact superpose b6e49 b6e72
          | exact resolve b6e72 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e72
        have b6e129 : (k x y) = (τ (σ (M.op y y))) := by
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
        have b6e130 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e129
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e129
          | exact resolve b6e129 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e129
        have b6e161 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e130
             grind)
          | exact superpose b6e130 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e162 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e161
        have b6e164 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e162
             have r₂ := b6e21
             grind)
          | exact resolve b6e162 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e162
        have b6e166 : False := by grind
        exact b6e166
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
            intro X0 X1
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e31 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
               have i₂ := b7e13 X0 (M.op X1 X1)
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e63
          have b7e66 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e65
            | exact resolve b7e65 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e67 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e64 y
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e64 (σ X0)
               grind)
            | exact superpose b7e64 b7e19
            | exact resolve b7e19 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e69 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e69
            | exact resolve b7e69 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e69
          have b7e228 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0)
               have i₂ := b7e31 X1 X0
               grind)
            | exact superpose b7e31 b7e13
            | exact resolve b7e13 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e432 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e228 (σ y) (σ x)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e228
            | exact resolve b7e228 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e433 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0
            first
            | (have i₁ := b7e228 (σ X0) (σ X0)
               have i₂ := b7e78 X0
               grind)
            | exact superpose b7e78 b7e228
            | exact resolve b7e228 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e228
          have b7e442 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e432
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e432
            | exact resolve b7e432 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e432
          have b7e447 : (σ x) = (M.op (σ (M.op y y)) (M.op (σ y) (σ (M.op y y)))) := by
            first
            | (have i₁ := b7e442
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e442
            | exact resolve b7e442 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e442
          have b7e448 : (σ x) = (σ y) := by
            first
            | (have i₁ := b7e447
               have i₂ := b7e433 y
               grind)
            | exact superpose b7e433 b7e447
            | exact resolve b7e447 b7e433
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e433 b7e447
          have b7e469 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e448
               grind)
            | exact superpose b7e448 b7e23
            | exact resolve b7e23 b7e448
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e448
          have b7e479 : False := by grind
          exact b7e479
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b8e112 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e944 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e112 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e945 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e944
               have r₂ := b8e23
               grind)
            | exact resolve b8e944 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e944
          have b8e947 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e945
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e945
            | exact resolve b8e945 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e945
          have b8e958 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e947
               grind)
            | exact superpose b8e947 b8e20
            | exact resolve b8e20 b8e947
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e947
          have b8e1037 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e958
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e958
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e958 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e958
          have b8e1038 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1037
          have b8e1040 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1038
               have r₂ := b8e21
               grind)
            | exact resolve b8e1038 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1038
          have b8e1043 : False := by grind
          exact b8e1043

/-- `Equation1323`: `x = y ◇ (((y ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1323 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1323 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1323.models_iff G M).mp hM
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
        have b1e45 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e47 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e48 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e47
             have r₂ := b1e23
             grind)
          | exact resolve b1e47 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
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
        have b2e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e132 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e501 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e132 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e132
          | (have j0 := b2e132 x y
             grind)
          | exact resolve b2e132 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e132
        have b2e504 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e501
        have b2e508 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e504
             have r₂ := b2e22
             grind)
          | exact resolve b2e504 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e504
        have b2e512 : False := by grind
        exact b2e512
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
        have b3e40 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e42 : x = y ∨ x = (k x y) := by grind
        clear b3e40
        have b3e43 : x = (k x y) := by
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
          have b5e44 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e46 : x = y ∨ x = (k x y) := by grind
          clear b5e44
          have b5e47 : x = (k x y) := by
            first
            | (have r₁ := b5e46
               have r₂ := b5e25
               grind)
            | exact resolve b5e46 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e46
          have b5e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e131 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e574 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e131 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e131
            | (have j0 := b5e131 x y
               grind)
            | exact resolve b5e131 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e131
          have b5e577 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e574
          have b5e580 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e577
               have r₂ := b5e24
               grind)
            | exact resolve b5e577 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e577
          have b5e584 : False := by grind
          exact b5e584
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
        have b6e46 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e48 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e46
        have b6e51 : x = (M.op x y) := by
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
          have b7e36 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e38 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e36
          have b7e39 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e38
               have r₂ := b7e25
               grind)
            | exact resolve b7e38 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e38
          have b7e40 : (σ x) = (σ (k x y)) := by
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
          have b7e43 : (k x y) = (τ (σ x)) := by
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
          have b7e44 : x = (k x y) := by
            first
            | (have i₁ := b7e43
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e43
            | exact resolve b7e43 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e43
          have b7e54 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e55 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e54
          have b7e57 : y = (M.op x y) := by
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e110 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e126 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e110
               have r₂ := b8e24
               grind)
            | exact resolve b8e110 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e110
          have b8e129 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e126
               have r₂ := b8e23
               grind)
            | exact resolve b8e126 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126
          have b8e130 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e129
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e129
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e129 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e129
          have b8e131 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e130
          have b8e132 : x = (M.op x y) := by
            first
            | (have r₁ := b8e131
               have r₂ := b8e22
               grind)
            | exact resolve b8e131 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e131
          have b8e133 : False := by grind
          exact b8e133

/-- `Equation1323`: `x = y ◇ (((y ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation1323 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1323 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1323.models_iff G M).mp hM
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
        have b2e123 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e55 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e558 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e123 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e123
          | (have j0 := b2e123 x y
             grind)
          | exact resolve b2e123 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e123
        have b2e561 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e558
        have b2e565 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e561
             have r₂ := b2e22
             grind)
          | exact resolve b2e561 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e561
        have b2e569 : False := by grind
        exact b2e569
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
          have b5e118 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e541 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e118 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e118
            | (have j0 := b5e118 x y
               grind)
            | exact resolve b5e118 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e118
          have b5e544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e541
          have b5e547 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e544
               have r₂ := b5e24
               grind)
            | exact resolve b5e544 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e544
          have b5e551 : False := by grind
          exact b5e551
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
          have b8e100 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e100
               have r₂ := b8e24
               grind)
            | exact resolve b8e100 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e100
          have b8e116 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e113
               have r₂ := b8e23
               grind)
            | exact resolve b8e113 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e117 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e116
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e116
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e116 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e116
          have b8e118 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e117
          have b8e119 : y = (M.op x y) := by
            first
            | (have r₁ := b8e118
               have r₂ := b8e22
               grind)
            | exact resolve b8e118 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e118
          have b8e120 : False := by grind
          exact b8e120

/-- `Equation1323`: `x = y ◇ (((y ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1323 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1323 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1323.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
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
      have b0e32 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
           have i₂ := b0e11 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
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
      have b0e76 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0)
           have i₂ := b0e32 X1 X0
           grind)
        | exact superpose b0e32 b0e11
        | exact resolve b0e11 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e101 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) (M.op (M.op X1 (M.op X0 X1)) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e76 (M.op X1 (M.op X0 X1)) (M.op X1 X1)
           have i₂ := b0e76 X1 X0
           grind)
        | exact superpose b0e76 b0e76
        | exact resolve b0e76 b0e76
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e102 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
        first
        | (have i₁ := b0e76 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e76
        | exact resolve b0e76 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e103 : y = (M.op (M.op x x) (M.op x x)) := by
        first
        | (have i₁ := b0e76 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e76
        | exact resolve b0e76 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e116 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
      have b0e124 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e125 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e55 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e141 : ∀ X0 : G, (M.op (M.op x x) (M.op X0 (M.op x x))) = (M.op (M.op (M.op y y) X0) y) := by
        intro X0
        first
        | (have i₁ := b0e32 X0 (M.op x x)
           have i₂ := b0e103
           grind)
        | exact superpose b0e103 b0e32
        | exact resolve b0e32 b0e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e287 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 (M.op (σ x) (σ x)))) = (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e32 X0 (M.op (σ x) (σ x))
           have i₂ := b0e102
           grind)
        | exact superpose b0e102 b0e32
        | exact resolve b0e32 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e532 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e124 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e124
        | (have j0 := b0e124 (τ X1) (τ X0)
           grind)
        | exact resolve b0e124 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e542 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e532 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e532
        | (have j0 := b0e532 X0 X1
           grind)
        | exact resolve b0e532 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e532
      have b0e545 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e542 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e542
        | (have j0 := b0e542 X0 X1
           grind)
        | exact resolve b0e542 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e542
      have b0e547 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e545 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e545
        | (have j0 := b0e545 X0 X1
           grind)
        | exact resolve b0e545 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e545
      have b0e548 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e547 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e547
        | (have j0 := b0e547 X0 X1
           grind)
        | exact resolve b0e547 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e547
      have b0e549 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e548 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e548
        | (have j0 := b0e548 X0 X1
           grind)
        | exact resolve b0e548 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e548
      have b0e550 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e549 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e549
        | (have j0 := b0e549 X0 X1
           grind)
        | exact resolve b0e549 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e549
      have b0e600 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e125 (τ X1) (τ X0)
           have i₂ := b0e43 X1 X0
           grind)
        | exact superpose b0e43 b0e125
        | (have j0 := b0e125 (τ X1) (τ X0)
           grind)
        | exact resolve b0e125 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e608 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e600 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e600
        | (have j0 := b0e600 X0 X1
           grind)
        | exact resolve b0e600 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e600
      have b0e611 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e608 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e608
        | (have j0 := b0e608 X0 X1
           grind)
        | exact resolve b0e608 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e608
      have b0e613 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e611 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e611
        | (have j0 := b0e611 X0 X1
           grind)
        | exact resolve b0e611 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e611
      have b0e614 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e613 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e613
        | (have j0 := b0e613 X0 X1
           grind)
        | exact resolve b0e613 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e613
      have b0e615 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e614 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e614
        | (have j0 := b0e614 X0 X1
           grind)
        | exact resolve b0e614 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e614
      have b0e616 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e615 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e615
        | (have j0 := b0e615 X0 X1
           grind)
        | exact resolve b0e615 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e615
      have b0e632 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e116
           have i₂ := b0e16 y x
           grind)
        | exact superpose b0e16 b0e116
        | (have j1 := b0e16 (σ y) (σ x)
           grind)
        | exact resolve b0e116 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116
      have b0e633 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e632
      have b0e1052 : x = (M.op (M.op (M.op y y) x) y) := by
        first
        | (have i₁ := b0e76 x x
           have i₂ := b0e141 x
           grind)
        | exact superpose b0e141 b0e76
        | exact resolve b0e76 b0e141
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e141
      have b0e4779 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e633
           grind)
        | exact superpose b0e633 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e633
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e633
           grind)
        | exact resolve b0e14 b0e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e633
      have b0e4787 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e4779
      have b0e4789 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e4787
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e4787
        | exact resolve b0e4787 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4787
      have b0e116789 : (σ x) = (M.op (M.op (M.op (σ y) (σ y)) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e76 (σ x) (σ x)
           have i₂ := b0e287 (σ x)
           grind)
        | exact superpose b0e287 b0e76
        | exact resolve b0e76 b0e287
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e76 b0e287
      have b0e137333 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (M.op (σ y) (σ x)) (σ x))) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e101 (σ x) (σ y)
           have i₂ := b0e4789
           grind)
        | exact superpose b0e4789 b0e101
        | exact resolve b0e101 b0e4789
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4789
      have b0e137344 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e137333
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e137333
        | exact resolve b0e137333 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137333
      have b0e137360 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e137344
           have i₂ := b0e102
           grind)
        | exact superpose b0e102 b0e137344
        | exact resolve b0e137344 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137344
      have b0e228239 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ y)
           have i₂ := b0e137360
           grind)
        | exact superpose b0e137360 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ y) (σ y)
           have r₂ := b0e137360
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e137360
           grind)
        | exact resolve b0e14 b0e137360
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e137360
      have b0e228241 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e228239
      have b0e228242 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e228241
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e228241
        | exact resolve b0e228241 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228241
      have b0e228264 : (k y y) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y y)
           have i₂ := b0e228242
           grind)
        | exact superpose b0e228242 b0e12
        | exact resolve b0e12 b0e228242
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228242
      have b0e228304 : (σ x) = (σ (k y x)) ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e228264
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e228264
        | exact resolve b0e228264 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228264
      have b0e228308 : (k y x) = (τ (σ x)) ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e228304
           grind)
        | exact superpose b0e228304 b0e12
        | exact resolve b0e12 b0e228304
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228304
      have b0e228352 : x = (k y x) ∨ y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e228308
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e228308
        | exact resolve b0e228308 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228308
      have b0e228353 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e550 y x
           grind)
        | (have r₁ := b0e228352
           have r₂ := b0e550 y x
           grind)
        | (have r₁ := b0e228352
           have r₂ := b0e550 y y
           grind)
        | exact resolve b0e228352 b0e550
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e550 b0e228352
      have b0e228723 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e616 y y
           have i₂ := b0e228353
           grind)
        | exact superpose b0e228353 b0e616
        | (have j0 := b0e616 y y
           grind)
        | (have r₁ := b0e616 y y
           have r₂ := b0e228353
           grind)
        | exact resolve b0e616 b0e228353
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228353
      have b0e228764 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e228723
      have b0e228765 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
      clear b0e228764
      have b0e228788 : x = (M.op (M.op y x) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e1052
           have i₂ := b0e228765
           grind)
        | exact superpose b0e228765 b0e1052
        | exact resolve b0e1052 b0e228765
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228765
      have b0e228867 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e228788
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e228788
        | exact resolve b0e228788 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228788
      have b0e228868 : y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e228867
      have b0e228873 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e228868
           grind)
        | exact superpose b0e228868 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e228868
           grind)
        | exact resolve b0e14 b0e228868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e228883 : x ≠ y ∨ x = (M.op x y) := by grind
      have b0e228886 : x = (k y x) ∨ x = (M.op x y) := by grind
      clear b0e228873
      have b0e228891 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e124 x y
           have i₂ := b0e228886
           grind)
        | exact superpose b0e228886 b0e124
        | (have j0 := b0e124 x y
           grind)
        | exact resolve b0e124 b0e228886
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e124 b0e228886
      have b0e228964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e228891
      have b0e230544 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e228964
           grind)
        | exact superpose b0e228964 b0e18
        | exact resolve b0e18 b0e228964
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228964
      have b0e230555 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e230544
           have i₂ := b0e228868
           grind)
        | exact superpose b0e228868 b0e230544
        | exact resolve b0e230544 b0e228868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228868 b0e230544
      have b0e230556 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
      clear b0e230555
      have b0e230557 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e230556
           have r₂ := b0e228883
           grind)
        | exact resolve b0e230556 b0e228883
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e228883 b0e230556
      have b0e230568 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ y) (σ x)) (M.op (σ y) (σ x))) (M.op (M.op (σ y) (σ x)) (σ x))) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e101 (σ x) (σ y)
           have i₂ := b0e230557
           grind)
        | exact superpose b0e230557 b0e101
        | exact resolve b0e101 b0e230557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230557
      have b0e230575 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e230568
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e230568
        | exact resolve b0e230568 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230568
      have b0e230583 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e230575
           have i₂ := b0e102
           grind)
        | exact superpose b0e102 b0e230575
        | exact resolve b0e230575 b0e102
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e102 b0e230575
      have b0e230622 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ y)
           have i₂ := b0e230583
           grind)
        | exact superpose b0e230583 b0e14
        | (have j0 := b0e14 (σ y) (σ y)
           grind)
        | (have r₁ := b0e14 (σ y) (σ y)
           have r₂ := b0e230583
           grind)
        | exact resolve b0e14 b0e230583
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230583
      have b0e230626 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by grind
      clear b0e230622
      have b0e230630 : (σ y) = (σ (k y y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e230626
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e230626
        | exact resolve b0e230626 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230626
      have b0e230715 : (k y y) = (τ (σ y)) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y y)
           have i₂ := b0e230630
           grind)
        | exact superpose b0e230630 b0e12
        | exact resolve b0e12 b0e230630
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230630
      have b0e230932 : y = (k y y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e230715
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e230715
        | exact resolve b0e230715 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e230715
      have b0e231317 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e616 y y
           have i₂ := b0e230932
           grind)
        | exact superpose b0e230932 b0e616
        | (have j0 := b0e616 y y
           grind)
        | (have r₁ := b0e616 y y
           have r₂ := b0e230932
           grind)
        | exact resolve b0e616 b0e230932
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e616 b0e230932
      have b0e231382 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
      clear b0e231317
      have b0e231383 : y = (M.op y y) ∨ x = (M.op x y) := by grind
      clear b0e231382
      have b0e231415 : x = (M.op (M.op y x) y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e1052
           have i₂ := b0e231383
           grind)
        | exact superpose b0e231383 b0e1052
        | exact resolve b0e1052 b0e231383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1052 b0e231383
      have b0e231553 : x = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e231415
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e231415
        | exact resolve b0e231415 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231415
      have b0e231554 : x = (M.op x y) := by grind
      clear b0e231553
      have b0e231565 : (M.op y y) = (M.op (M.op (M.op y x) (M.op y x)) (M.op (M.op y x) x)) := by
        first
        | (have i₁ := b0e101 x y
           have i₂ := b0e231554
           grind)
        | exact superpose b0e231554 b0e101
        | exact resolve b0e101 b0e231554
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101
      have b0e231579 : (M.op (M.op x x) (M.op x x)) = (M.op y y) := by
        first
        | (have i₁ := b0e231565
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e231565
        | exact resolve b0e231565 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231565
      have b0e231587 : y = (M.op y y) := by
        first
        | (have i₁ := b0e231579
           have i₂ := b0e103
           grind)
        | exact superpose b0e103 b0e231579
        | exact resolve b0e231579 b0e103
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103 b0e231579
      have b0e231703 : y ≠ y ∨ y = (k y y) := by
        first
        | (have i₁ := b0e14 y y
           have i₂ := b0e231587
           grind)
        | exact superpose b0e231587 b0e14
        | (have j0 := b0e14 y y
           grind)
        | (have r₁ := b0e14 y y
           have r₂ := b0e231587
           grind)
        | exact resolve b0e14 b0e231587
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231587
      have b0e231710 : y = (k y y) := by grind
      clear b0e231703
      have b0e232186 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e125 y y
           have i₂ := b0e231710
           grind)
        | exact superpose b0e231710 b0e125
        | (have j0 := b0e125 y y
           grind)
        | exact resolve b0e125 b0e231710
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e125 b0e231710
      have b0e232265 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e232186
      have b0e232266 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear b0e232265
      have b0e232553 : (σ x) = (M.op (M.op (σ y) (σ x)) (σ y)) := by
        first
        | (have i₁ := b0e116789
           have i₂ := b0e232266
           grind)
        | exact superpose b0e232266 b0e116789
        | exact resolve b0e116789 b0e232266
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e116789 b0e232266
      have b0e232620 : (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e232553
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e232553
        | exact resolve b0e232553 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232553
      have b0e232668 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e232620
           grind)
        | exact superpose b0e232620 b0e18
        | exact resolve b0e18 b0e232620
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e232620
      have b0e232686 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e232668
           have i₂ := b0e231554
           grind)
        | exact superpose b0e231554 b0e232668
        | exact resolve b0e232668 b0e231554
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e231554 b0e232668
      have b0e232687 : False := by grind
      exact b0e232687
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
        have b2e112 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e514 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e112 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e112
          | (have j0 := b2e112 y x
             grind)
          | exact resolve b2e112 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e112
        have b2e517 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e514
        have b2e521 : (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e517
             have r₂ := b2e22
             grind)
          | exact resolve b2e517 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e517
        have b2e525 : False := by grind
        exact b2e525
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b4e30 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
          have b4e31 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
               have i₂ := b4e13 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
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
          have b4e64 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X0 X0)
               have i₂ := b4e31 X1 X0
               grind)
            | exact superpose b4e31 b4e13
            | exact resolve b4e13 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e69 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
          have b4e104 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b4e110 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e111 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e130 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (M.op (σ X0) (M.op X1 (σ X0)))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e64 (σ X0) X1
               have i₂ := b4e47 X0 X0
               grind)
            | exact superpose b4e47 b4e64
            | (have j1 := b4e47 X0 X0
               grind)
            | exact resolve b4e64 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e134 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e64 (σ x) (σ y)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e64
            | exact resolve b4e64 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e135 : ∀ X0 X1 : G, (σ X1) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e64 (σ X0) (σ X1)
               have i₂ := b4e47 X1 X0
               grind)
            | exact superpose b4e47 b4e64
            | (have j1 := b4e47 X1 X0
               grind)
            | exact resolve b4e64 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e136 : y = (M.op (M.op x x) (M.op x y)) := by
            first
            | (have i₁ := b4e64 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e64
            | exact resolve b4e64 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e142 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (M.op (σ X0) (M.op X1 (σ X0)))) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e130 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e160 : (M.op x x) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b4e64 (M.op x y) (M.op x x)
               have i₂ := b4e136
               grind)
            | exact superpose b4e136 b4e64
            | exact resolve b4e64 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e533 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e110 (τ X1) (τ X0)
               have i₂ := b4e69 X1 X0
               grind)
            | exact superpose b4e69 b4e110
            | (have j0 := b4e110 (τ X1) (τ X0)
               grind)
            | exact resolve b4e110 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e541 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e533 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e533
            | (have j0 := b4e533 X0 X1
               grind)
            | exact resolve b4e533 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e533
          have b4e544 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e541 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e541
            | (have j0 := b4e541 X0 X1
               grind)
            | exact resolve b4e541 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e541
          have b4e546 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e544 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e544
            | (have j0 := b4e544 X0 X1
               grind)
            | exact resolve b4e544 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e544
          have b4e547 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e546 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e546
            | (have j0 := b4e546 X0 X1
               grind)
            | exact resolve b4e546 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e546
          have b4e548 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e547 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e547
            | (have j0 := b4e547 X0 X1
               grind)
            | exact resolve b4e547 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e547
          have b4e549 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e548 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e548
            | (have j0 := b4e548 X0 X1
               grind)
            | exact resolve b4e548 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e548
          have b4e563 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e111 (τ X1) (τ X0)
               have i₂ := b4e69 X1 X0
               grind)
            | exact superpose b4e69 b4e111
            | (have j0 := b4e111 (τ X1) (τ X0)
               grind)
            | exact resolve b4e111 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e572 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e563 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e563
            | (have j0 := b4e563 X0 X1
               grind)
            | exact resolve b4e563 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e563
          have b4e575 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e572 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e572
            | (have j0 := b4e572 X0 X1
               grind)
            | exact resolve b4e572 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e572
          have b4e577 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e575 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e575
            | (have j0 := b4e575 X0 X1
               grind)
            | exact resolve b4e575 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e575
          have b4e578 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e577 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e577
            | (have j0 := b4e577 X0 X1
               grind)
            | exact resolve b4e577 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e577
          have b4e579 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e578 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e578
            | (have j0 := b4e578 X0 X1
               grind)
            | exact resolve b4e578 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e578
          have b4e580 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e579 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e579
            | (have j0 := b4e579 X0 X1
               grind)
            | exact resolve b4e579 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e579
          have b4e591 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e104
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e104
            | (have j1 := b4e18 (σ y) (σ x)
               grind)
            | exact resolve b4e104 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104
          have b4e592 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e591
          have b4e5481 : ∀ X0 X1 : G, (M.op (σ (k (τ X0) (τ X0))) (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e142 (τ X0) X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e142
            | exact resolve b4e142 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e5528 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e5481 X0 X1
               have i₂ := b4e30 X0 (τ X0)
               grind)
            | exact superpose b4e30 b4e5481
            | (have j0 := b4e5481 X0 X1
               grind)
            | exact resolve b4e5481 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e5481
          have b4e5551 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 (M.op X1 X0))) = X1 ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e5528 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e5528
            | (have j0 := b4e5528 X0 X1
               grind)
            | exact resolve b4e5528 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5528
          have b4e5619 : y = (M.op (k x x) (M.op x y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e5551 x y
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e5551
            | (have j0 := b4e5551 x x
               grind)
            | exact resolve b4e5551 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5551
          have b4e6519 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e592
               grind)
            | exact superpose b4e592 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e592
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e592
               grind)
            | exact resolve b4e16 b4e592
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e592
          have b4e6527 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e6519
          have b4e6529 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e6527
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e6527
            | exact resolve b4e6527 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6527
          have b4e14108 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op (σ (τ X0)) (σ (τ X0))) (M.op (σ (τ X0)) (σ (τ (k X0 X1))))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e135 (τ X0) (τ X1)
               have i₂ := b4e69 X1 X0
               grind)
            | exact superpose b4e69 b4e135
            | (have j0 := b4e135 (τ X0) (τ X1)
               grind)
            | exact resolve b4e135 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69 b4e135
          have b4e14211 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op (σ (τ X0)) (σ (τ X0))) (M.op (σ (τ X0)) (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14108 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e14108
            | (have j0 := b4e14108 X0 X1
               grind)
            | exact resolve b4e14108 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14108
          have b4e14247 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14211 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e14211
            | (have j0 := b4e14211 X0 X1
               grind)
            | exact resolve b4e14211 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14211
          have b4e14282 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) = X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14247 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e14247
            | (have j0 := b4e14247 X0 X1
               grind)
            | exact resolve b4e14247 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14247
          have b4e14311 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14282 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e14282
            | (have j0 := b4e14282 X0 X1
               grind)
            | exact resolve b4e14282 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14282
          have b4e14338 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) = X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14311 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e14311
            | (have j0 := b4e14311 X0 X1
               grind)
            | exact resolve b4e14311 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14311
          have b4e14363 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e14338 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e14338
            | (have j0 := b4e14338 X0 X1
               grind)
            | exact resolve b4e14338 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14338
          have b4e14376 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (k X0 X1))) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e14363 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e14363
            | (have j0 := b4e14363 X0 X1
               grind)
            | exact resolve b4e14363 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14363
          have b4e132136 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e6529
               grind)
            | exact superpose b4e6529 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e6529
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e6529
               grind)
            | exact resolve b4e17 b4e6529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6529
          have b4e132138 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e132136
          have b4e132140 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e132138
               have r₂ := b4e25
               grind)
            | exact resolve b4e132138 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132138
          have b4e132141 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e132140
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e132140
            | exact resolve b4e132140 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132140
          have b4e132217 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e132141
               grind)
            | exact superpose b4e132141 b4e14
            | exact resolve b4e14 b4e132141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132141
          have b4e132260 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e132217
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e132217
            | exact resolve b4e132217 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132217
          have b4e132261 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b4e580 y x
               grind)
            | (have r₁ := b4e132260
               have r₂ := b4e580 y x
               grind)
            | exact resolve b4e132260 b4e580
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e580 b4e132260
          have b4e132309 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e132261
               grind)
            | exact superpose b4e132261 b4e14
            | exact resolve b4e14 b4e132261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132261
          have b4e132460 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e132309
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e132309
            | exact resolve b4e132309 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132309
          have b4e132461 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e549 y x
               grind)
            | (have r₁ := b4e132460
               have r₂ := b4e549 y x
               grind)
            | exact resolve b4e132460 b4e549
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e549 b4e132460
          have b4e132466 : (M.op x x) = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e160
               have i₂ := b4e132461
               grind)
            | exact superpose b4e132461 b4e160
            | exact resolve b4e160 b4e132461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e160
          have b4e132471 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e16 y x
               have i₂ := b4e132461
               grind)
            | exact superpose b4e132461 b4e16
            | (have j0 := b4e16 y x
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e132461
               grind)
            | exact resolve b4e16 b4e132461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132472 : x = (M.op (M.op y y) (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e64 y x
               have i₂ := b4e132461
               grind)
            | exact superpose b4e132461 b4e64
            | exact resolve b4e64 b4e132461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e132481 : x = (k y x) ∨ x = (M.op x y) := by grind
          clear b4e132471
          have b4e132518 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e110 x y
               have i₂ := b4e132481
               grind)
            | exact superpose b4e132481 b4e110
            | (have j0 := b4e110 x y
               grind)
            | exact resolve b4e110 b4e132481
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e110 b4e132481
          have b4e132568 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
          clear b4e132518
          have b4e132877 : x = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e132472
               have i₂ := b4e132466
               grind)
            | exact superpose b4e132466 b4e132472
            | exact resolve b4e132472 b4e132466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132466 b4e132472
          have b4e132920 : x = (M.op x y) ∨ x = (M.op x x) := by grind
          clear b4e132877
          have b4e132968 : y = (M.op (k x x) x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e5619
               have i₂ := b4e132920
               grind)
            | exact superpose b4e132920 b4e5619
            | exact resolve b4e5619 b4e132920
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5619 b4e132920
          have b4e132981 : y = (M.op (k x x) x) ∨ x = (M.op x x) := by grind
          clear b4e132968
          have b4e133302 : (M.op (M.op x x) (M.op x y)) = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e64 x (k x x)
               have i₂ := b4e132981
               grind)
            | exact superpose b4e132981 b4e64
            | exact resolve b4e64 b4e132981
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64 b4e132981
          have b4e133316 : y = (k x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e133302
               have i₂ := b4e136
               grind)
            | exact superpose b4e136 b4e133302
            | exact resolve b4e133302 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133302
          have b4e133525 : x = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14376 x x
               have i₂ := b4e133316
               grind)
            | exact superpose b4e133316 b4e14376
            | (have j0 := b4e14376 x x
               grind)
            | exact resolve b4e14376 b4e133316
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e14376 b4e133316
          have b4e133540 : x = (M.op (M.op x x) (M.op x y)) ∨ x = (M.op x x) := by grind
          clear b4e133525
          have b4e133704 : x = y ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e133540
               have i₂ := b4e136
               grind)
            | exact superpose b4e136 b4e133540
            | exact resolve b4e133540 b4e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133540
          have b4e133708 : x = (M.op x x) := by
            first
            | (have r₁ := b4e133704
               have r₂ := b4e26
               grind)
            | exact resolve b4e133704 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133704
          have b4e133728 : y = (M.op x (M.op x y)) := by
            first
            | (have i₁ := b4e136
               have i₂ := b4e133708
               grind)
            | exact superpose b4e133708 b4e136
            | exact resolve b4e136 b4e133708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e133751 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b4e16 x x
               have i₂ := b4e133708
               grind)
            | exact superpose b4e133708 b4e16
            | (have j0 := b4e16 x x
               grind)
            | (have r₁ := b4e16 x x
               have r₂ := b4e133708
               grind)
            | exact resolve b4e16 b4e133708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133756 : x = (k x x) := by grind
          clear b4e133751
          have b4e133985 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b4e111 x x
               have i₂ := b4e133756
               grind)
            | exact superpose b4e133756 b4e111
            | (have j0 := b4e111 x x
               grind)
            | exact resolve b4e111 b4e133756
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e111 b4e133756
          have b4e134042 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e133985
          have b4e134043 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b4e134042
          have b4e134244 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e134
               have i₂ := b4e134043
               grind)
            | exact superpose b4e134043 b4e134
            | exact resolve b4e134 b4e134043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e237323 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e132568
               grind)
            | exact superpose b4e132568 b4e20
            | exact resolve b4e20 b4e132568
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132568
          have b4e237341 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e237323
               have i₂ := b4e132461
               grind)
            | exact superpose b4e132461 b4e237323
            | exact resolve b4e237323 b4e132461
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e132461 b4e237323
          have b4e237344 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
          clear b4e237341
          have b4e237345 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e237344
               have r₂ := b4e26
               grind)
            | exact resolve b4e237344 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e237344
          have b4e237354 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e134244
               have i₂ := b4e237345
               grind)
            | exact superpose b4e237345 b4e134244
            | exact resolve b4e134244 b4e237345
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134244 b4e237345
          have b4e237378 : (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e237354
               have i₂ := b4e134043
               grind)
            | exact superpose b4e134043 b4e237354
            | exact resolve b4e237354 b4e134043
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134043 b4e237354
          have b4e237387 : x = (M.op x y) := by
            first
            | (have r₁ := b4e237378
               have r₂ := b4e25
               grind)
            | exact resolve b4e237378 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e237378
          have b4e237411 : y = (M.op x x) := by
            first
            | (have i₁ := b4e133728
               have i₂ := b4e237387
               grind)
            | exact superpose b4e237387 b4e133728
            | exact resolve b4e133728 b4e237387
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133728 b4e237387
          have b4e237453 : x = y := by
            first
            | (have i₁ := b4e237411
               have i₂ := b4e133708
               grind)
            | exact superpose b4e133708 b4e237411
            | exact resolve b4e237411 b4e133708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133708 b4e237411
          have b4e237467 : False := by grind
          exact b4e237467
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
          have b5e106 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e41 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e521 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e106 y x
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e106
            | (have j0 := b5e106 y x
               grind)
            | exact resolve b5e106 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e106
          have b5e524 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e521
          have b5e527 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e524
               have r₂ := b5e24
               grind)
            | exact resolve b5e524 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e524
          have b5e531 : False := by grind
          exact b5e531
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
        · have b8e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (M.op X1 X1) X0) X1)) = X0 := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b8e27 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 (M.op (M.op (M.op (M.op X1 X1) (M.op X1 X1)) X0) (M.op X1 X1)) X1
               have i₂ := b8e13 X0 (M.op X1 X1)
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
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
          have b8e39 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          clear b8e26
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
          have b8e44 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e25 X1 X0
               have i₂ := b8e18 (τ X1) X0
               grind)
            | exact superpose b8e18 b8e25
            | (have j1 := b8e18 (τ X1) X0
               grind)
            | exact resolve b8e25 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25
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
          have b8e58 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X1 X0))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op X0 X0)
               have i₂ := b8e27 X1 X0
               grind)
            | exact superpose b8e27 b8e13
            | exact resolve b8e13 b8e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e27
          have b8e102 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e108 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e109 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e120 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X0) = X0 := by
            intro X0
            first
            | (have i₁ := b8e58 (M.op X0 X0) X0
               have i₂ := b8e58 X0 X0
               grind)
            | exact superpose b8e58 b8e58
            | exact resolve b8e58 b8e58
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e133 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               have i₂ := b8e120 X0
               grind)
            | exact superpose b8e120 b8e16
            | (have j0 := b8e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | (have r₁ := b8e16 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               have r₂ := b8e120 X0
               grind)
            | exact resolve b8e16 b8e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120
          have b8e134 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op (M.op X0 X0) (M.op X0 X0))) := by
            intro X0
            first
            | (have j0 := b8e133 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e319 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e44 X0 (σ X0)
               have i₂ := b8e14 X0
               grind)
            | exact superpose b8e14 b8e44
            | exact resolve b8e44 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e349 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e319 X0 X1
               have i₂ := b8e19 X0 X1
               grind)
            | exact superpose b8e19 b8e319
            | (have j0 := b8e319 X0 X1
               grind)
            | exact resolve b8e319 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e319
          have b8e476 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e108 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e108
            | (have j0 := b8e108 (τ X1) (τ X0)
               grind)
            | exact resolve b8e108 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e483 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e476 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e476
            | (have j0 := b8e476 X0 X1
               grind)
            | exact resolve b8e476 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e476
          have b8e486 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e483 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e483
            | (have j0 := b8e483 X0 X1
               grind)
            | exact resolve b8e483 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e483
          have b8e488 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e486 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e486
            | (have j0 := b8e486 X0 X1
               grind)
            | exact resolve b8e486 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e486
          have b8e489 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e488 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e488
            | (have j0 := b8e488 X0 X1
               grind)
            | exact resolve b8e488 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e488
          have b8e490 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e489 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e489
            | (have j0 := b8e489 X0 X1
               grind)
            | exact resolve b8e489 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e489
          have b8e491 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e490 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e490
            | (have j0 := b8e490 X0 X1
               grind)
            | exact resolve b8e490 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e490
          have b8e504 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e109 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e109
            | (have j0 := b8e109 (τ X1) (τ X0)
               grind)
            | exact resolve b8e109 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46
          have b8e511 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e504 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e504
            | (have j0 := b8e504 X0 X1
               grind)
            | exact resolve b8e504 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e504
          have b8e514 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e511 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e511
            | (have j0 := b8e511 X0 X1
               grind)
            | exact resolve b8e511 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e511
          have b8e516 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e514 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e514
            | (have j0 := b8e514 X0 X1
               grind)
            | exact resolve b8e514 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e514
          have b8e517 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e516 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e516
            | (have j0 := b8e516 X0 X1
               grind)
            | exact resolve b8e516 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e516
          have b8e518 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e517 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e517
            | (have j0 := b8e517 X0 X1
               grind)
            | exact resolve b8e517 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e517
          have b8e519 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e518 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e518
            | (have j0 := b8e518 X0 X1
               grind)
            | exact resolve b8e518 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e518
          have b8e528 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e102
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e102
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e102 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e102
          have b8e529 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e528
          have b8e700 : ∀ X0 : G, (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))) = (k X0 (τ (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))))) := by
            intro X0
            first
            | (have i₁ := b8e39 X0 (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0)))
               have i₂ := b8e134 (σ X0)
               grind)
            | exact superpose b8e134 b8e39
            | exact resolve b8e39 b8e134
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e39 b8e134
          have b8e6833 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e529
               grind)
            | exact superpose b8e529 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e529
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e529
               grind)
            | exact resolve b8e16 b8e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6834 : (σ x) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e58 (σ y) (σ x)
               have i₂ := b8e529
               grind)
            | exact superpose b8e529 b8e58
            | exact resolve b8e58 b8e529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58 b8e529
          have b8e6841 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e6833
          have b8e6843 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e6841
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e6841
            | exact resolve b8e6841 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6841
          have b8e144948 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e6843
               grind)
            | exact superpose b8e6843 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e6843
               grind)
            | exact resolve b8e16 b8e6843
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e6843
          have b8e144953 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e144948
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e144948
            | exact resolve b8e144948 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144948
          have b8e144954 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e144953
          have b8e207350 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e700 y
               have i₂ := b8e6834
               grind)
            | exact superpose b8e6834 b8e700
            | exact resolve b8e700 b8e6834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e700 b8e6834
          have b8e207359 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e207350
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e207350
            | exact resolve b8e207350 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207350
          have b8e207361 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b8e491 y x
               grind)
            | (have r₁ := b8e207359
               have r₂ := b8e491 y x
               grind)
            | exact resolve b8e207359 b8e491
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e491 b8e207359
          have b8e207367 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e207361
               grind)
            | exact superpose b8e207361 b8e20
            | exact resolve b8e20 b8e207361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e207371 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e207361
               grind)
            | exact superpose b8e207361 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e207361
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e207361
               grind)
            | exact resolve b8e17 b8e207361
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207361
          have b8e207376 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e207371
          have b8e207379 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e207376
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e207376
            | exact resolve b8e207376 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207376
          have b8e207393 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e207379
               grind)
            | exact superpose b8e207379 b8e14
            | exact resolve b8e14 b8e207379
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207379
          have b8e207438 : y = (k y x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e207393
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e207393
            | exact resolve b8e207393 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207393
          have b8e207439 : y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have j1 := b8e519 y x
               grind)
            | (have r₁ := b8e207438
               have r₂ := b8e519 y x
               grind)
            | exact resolve b8e207438 b8e519
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e519 b8e207438
          have b8e207442 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e207439
               grind)
            | exact superpose b8e207439 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e207439
               grind)
            | exact resolve b8e16 b8e207439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e207451 : x ≠ y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
          have b8e207455 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
          clear b8e207442
          have b8e207464 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e108 x y
               have i₂ := b8e207455
               grind)
            | exact superpose b8e207455 b8e108
            | (have j0 := b8e108 x y
               grind)
            | exact resolve b8e108 b8e207455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e108
          have b8e207536 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
          clear b8e207464
          have b8e208322 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e207536
               grind)
            | exact superpose b8e207536 b8e20
            | exact resolve b8e20 b8e207536
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207536
          have b8e208331 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e208322
               have i₂ := b8e207439
               grind)
            | exact superpose b8e207439 b8e208322
            | exact resolve b8e208322 b8e207439
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207439 b8e208322
          have b8e208332 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e208331
          have b8e208333 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
          clear b8e208332
          have b8e208334 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e208333
               have r₂ := b8e207451
               grind)
            | exact resolve b8e208333 b8e207451
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207451 b8e208333
          have b8e208345 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e208334
               grind)
            | exact superpose b8e208334 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e208334
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e208334
               grind)
            | exact resolve b8e17 b8e208334
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208334
          have b8e208350 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e208345
          have b8e208351 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
          clear b8e208350
          have b8e208355 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e208351
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e208351
            | exact resolve b8e208351 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208351
          have b8e208366 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e208355
               have i₂ := b8e207455
               grind)
            | exact superpose b8e207455 b8e208355
            | exact resolve b8e208355 b8e207455
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207455 b8e208355
          have b8e208466 : x = (M.op x y) ∨ (σ x) = (σ y) := by grind
          clear b8e208366
          have b8e208488 : x ≠ x ∨ x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e208466
               grind)
            | exact superpose b8e208466 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e208466
               grind)
            | exact resolve b8e17 b8e208466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e208499 : y = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e208488
          have b8e208516 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e109 x y
               have i₂ := b8e208499
               grind)
            | exact superpose b8e208499 b8e109
            | (have j0 := b8e109 x y
               grind)
            | exact resolve b8e109 b8e208499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e208566 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e208516
          have b8e225697 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e208566
               grind)
            | exact superpose b8e208566 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e208566
               grind)
            | exact resolve b8e16 b8e208566
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208566
          have b8e225700 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e225697
          have b8e225703 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e225700
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e225700
            | exact resolve b8e225700 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225700
          have b8e225709 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e225703
               grind)
            | exact superpose b8e225703 b8e20
            | exact resolve b8e20 b8e225703
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225703
          have b8e225716 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e225709
               have i₂ := b8e208466
               grind)
            | exact superpose b8e208466 b8e225709
            | exact resolve b8e225709 b8e208466
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208466 b8e225709
          have b8e225719 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e225716
          have b8e225720 : (σ x) = (σ (k y x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
          clear b8e225719
          have b8e225721 : (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e225720
               have i₂ := b8e208499
               grind)
            | exact superpose b8e208499 b8e225720
            | exact resolve b8e225720 b8e208499
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e208499 b8e225720
          have b8e225832 : (σ x) = (σ y) ∨ x = y := by grind
          clear b8e225721
          have b8e225861 : y = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b8e14 y
               have i₂ := b8e225832
               grind)
            | exact superpose b8e225832 b8e14
            | exact resolve b8e14 b8e225832
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225832
          have b8e226119 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e225861
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e225861
            | exact resolve b8e225861 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225861
          have b8e226120 : x = y := by grind
          clear b8e226119
          have b8e226123 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e226120
               grind)
            | exact superpose b8e226120 b8e22
            | exact resolve b8e22 b8e226120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e226133 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e144954
               have i₂ := b8e226120
               grind)
            | exact superpose b8e226120 b8e144954
            | exact resolve b8e144954 b8e226120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144954
          have b8e226135 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e207367
               have i₂ := b8e226120
               grind)
            | exact superpose b8e226120 b8e207367
            | exact resolve b8e207367 b8e226120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e207367 b8e226120
          have b8e226140 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b8e226135
          have b8e226142 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
          clear b8e226133
          have b8e226143 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by grind
          clear b8e226142
          have b8e228712 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e349 x x
               have i₂ := b8e226143
               grind)
            | exact superpose b8e226143 b8e349
            | (have j0 := b8e349 x x
               grind)
            | exact resolve b8e349 b8e226143
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e349 b8e226143
          have b8e228889 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
          clear b8e228712
          have b8e229084 : x = (M.op x x) := by
            first
            | (have r₁ := b8e228889
               have r₂ := b8e226140
               grind)
            | exact resolve b8e228889 b8e226140
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e226140 b8e228889
          have b8e229249 : False := by grind
          exact b8e229249
