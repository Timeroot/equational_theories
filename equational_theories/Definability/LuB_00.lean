import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3888`: `x ◇ x = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation3888 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3888 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3888.models_iff G M).mp hM
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
        have b1e48 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e50 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e48
        have b1e51 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e50
             have r₂ := b1e23
             grind)
          | exact resolve b1e50 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50
        have b1e52 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e51
          | exact resolve b1e51 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e51
        have b1e53 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e52
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e52
          | exact resolve b1e52 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e52
        have b1e54 : False := by grind
        exact b1e54
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
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e265 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e50 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e1487 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e265 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e265
          | (have j0 := b2e265 x y
             grind)
          | exact resolve b2e265 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e265
        have b2e1494 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e1487
        have b2e1500 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1494
             have r₂ := b2e22
             grind)
          | exact resolve b2e1494 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1494
        have b2e1504 : False := by grind
        exact b2e1504
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
        have b3e48 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        clear b3e48
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
          have b5e42 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
          clear b5e42
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
          have b5e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e253 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e50 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e1622 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e253 x y
               have i₂ := b5e47
               grind)
            | exact superpose b5e47 b5e253
            | (have j0 := b5e253 x y
               grind)
            | exact resolve b5e253 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e253
          have b5e1627 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e1622
          have b5e1632 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1627
               have r₂ := b5e24
               grind)
            | exact resolve b5e1627 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1627
          have b5e1636 : False := by grind
          exact b5e1636
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
        have b6e52 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
        have b6e54 : x = (M.op x y) ∨ y = (M.op x y) := by grind
        clear b6e52
        have b6e57 : y = (M.op x y) := by
          first
          | (have r₁ := b6e54
             have r₂ := b6e21
             grind)
          | exact resolve b6e54 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e54
        have b6e60 : False := by grind
        exact b6e60
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
          have b7e40 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          clear b7e40
          have b7e44 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e43
               have r₂ := b7e25
               grind)
            | exact resolve b7e43 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e43
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
          have b7e59 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
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
          have b7e60 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b7e59
          have b7e62 : x = (M.op x y) := by
            first
            | (have r₁ := b7e60
               have r₂ := b7e21
               grind)
            | exact resolve b7e60 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e64 : False := by grind
          exact b7e64
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
          have b8e47 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e253 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e277 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e253
               have r₂ := b8e24
               grind)
            | exact resolve b8e253 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e253
          have b8e280 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e277
               have r₂ := b8e23
               grind)
            | exact resolve b8e277 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e277
          have b8e281 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e280
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e280
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e280 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e280
          have b8e282 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e281
          have b8e283 : y = (M.op x y) := by
            first
            | (have r₁ := b8e282
               have r₂ := b8e22
               grind)
            | exact resolve b8e282 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e282
          have b8e284 : False := by grind
          exact b8e284

/-- `Equation4409`: `x ◇ (x ◇ y) = (y ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_x_pxy_Equation4409 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4409 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4409.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (x) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e40 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ x) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e14
        | (have j0 := b0e14 (σ x) (σ y)
           grind)
        | (have r₁ := b0e14 (σ x) (σ y)
           have r₂ := b0e20
           grind)
        | exact resolve b0e14 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : x ≠ x ∨ (M.op x y) = (k x y) := by
        first
        | (have i₁ := b0e14 x y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e14
        | (have j0 := b0e14 x y
           grind)
        | (have r₁ := b0e14 x y
           have r₂ := b0e19
           grind)
        | exact resolve b0e14 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : (M.op x y) = (k x y) := by grind
      clear b0e41
      have b0e43 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
      clear b0e40
      have b0e44 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e43
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e43
        | exact resolve b0e43 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e45 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e42
           grind)
        | exact superpose b0e42 b0e44
        | exact resolve b0e44 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e44
      have b0e46 : False := by grind
      exact b0e46
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X1) := by
          intro X0 X1
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : x = (M.op y x) := by grind
        have b1e21 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e27 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b1e12 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e29 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 X1
             have i₂ := b1e12 X2 X1
             grind)
          | exact superpose b1e12 b1e12
          | exact resolve b1e12 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 (M.op X1 X1)) = (k X1 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X1 (M.op X1 X1)
             have i₂ := b1e12 X0 X1
             grind)
          | exact superpose b1e12 b1e15
          | (have j0 := b1e15 X1 (M.op X1 X1)
             grind)
          | (have r₁ := b1e15 (M.op (M.op X1 X1) X1) (M.op X1 X1)
             have r₂ := b1e12 (M.op X1 X1) X1
             grind)
          | exact resolve b1e15 b1e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e36 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
          first
          | (have i₁ := b1e36
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e36
          | exact resolve b1e36 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e36
        have b1e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
        have b1e59 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e60 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X1 X2
             have i₂ := b1e17 X2 X0
             grind)
          | (have i₁ := b1e12 X0 X1
             have i₂ := b1e17 X0 (M.op X1 X1)
             grind)
          | exact superpose b1e17 b1e12
          | (have j1 := b1e17 X2 X0
             grind)
          | exact resolve b1e12 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e62 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e59 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e64 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b1e60 X0 X1 X2
             have j1 := b1e15 X2 X0
             grind)
          | (have r₁ := b1e60 X1 X1 X2
             have r₂ := b1e15 (M.op X1 X2) X1
             grind)
          | (have r₁ := b1e60 X1 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e60 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e60
        have b1e65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e62 X0 X1
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e62 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e62 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e62
        have b1e82 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e21
          | exact resolve b1e21 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e105 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e29 X0 x y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e29
          | exact resolve b1e29 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e29
        have b1e113 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e105 X0
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e105
          | exact resolve b1e105 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e105
        have b1e161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (k X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e65 (σ X1) (σ X0)
             have i₂ := b1e18 X0 X1
             grind)
          | exact superpose b1e18 b1e65
          | exact resolve b1e65 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e314 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 (M.op X0 x)) ∨ (M.op (M.op X0 x) X1) = (k (M.op X0 x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e64 X1 X0 (M.op X0 x)
             have i₂ := b1e113 X0
             grind)
          | exact superpose b1e113 b1e64
          | (have j0 := b1e64 X1 X1 (M.op X0 x)
             grind)
          | exact resolve b1e64 b1e113
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e356 : ∀ X0 : G, x = (M.op X0 x) ∨ (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b1e113 x
             have i₂ := b1e64 X0 x x
             grind)
          | exact superpose b1e64 b1e113
          | (have j1 := b1e64 X0 x x
             grind)
          | exact resolve b1e113 b1e64
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e64 b1e113
        have b1e406 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
          intro X0
          first
          | (have j0 := b1e356 X0
             have j1 := b1e15 x X0
             grind)
          | (have r₁ := b1e356 x
             have r₂ := b1e15 x x
             grind)
          | exact resolve b1e356 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e356
        have b1e422 : ∀ X0 X1 : G, (M.op (M.op X0 x) X1) = (k (M.op X0 x) X1) := by
          intro X0 X1
          first
          | (have j0 := b1e314 X0 X1
             have j1 := b1e15 (M.op X0 x) X1
             grind)
          | (have r₁ := b1e314 X0 X1
             have r₂ := b1e15 (M.op X0 x) X1
             grind)
          | exact resolve b1e314 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e314
        have b1e486 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b1e35 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e35 X0 X1
             have i₂ := b1e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b1e17 b1e35
          | (have j1 := b1e17 X1 X0
             grind)
          | (have r₁ := b1e35 X0 (M.op X0 X0)
             have r₂ := b1e17 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
             grind)
          | exact resolve b1e35 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e35
        have b1e506 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b1e486 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e486
        have b1e513 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e506 X0 X1
             have j1 := b1e15 X1 X0
             grind)
          | (have r₁ := b1e506 X1 X0
             have r₂ := b1e15 X0 X1
             grind)
          | exact resolve b1e506 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e506
        have b1e606 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b1e55 x x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e55
          | exact resolve b1e55 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e682 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
        clear b1e606
        have b1e712 : (σ y) = (σ (k x x)) := by
          first
          | (have r₁ := b1e682
             have r₂ := b1e39
             grind)
          | exact resolve b1e682 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e682
        have b1e738 : (σ y) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e712
             have i₂ := b1e406 x
             grind)
          | exact superpose b1e406 b1e712
          | exact resolve b1e712 b1e406
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e406 b1e712
        have b1e742 : (M.op x x) = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e738
             grind)
          | exact superpose b1e738 b1e13
          | exact resolve b1e13 b1e738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e743 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (k (σ y) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 (M.op x x) X0
             have i₂ := b1e738
             grind)
          | exact superpose b1e738 b1e18
          | exact resolve b1e18 b1e738
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e738
        have b1e758 : ∀ X0 : G, (σ (k (M.op x x) X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b1e743 X0
             have i₂ := b1e18 y X0
             grind)
          | exact superpose b1e18 b1e743
          | exact resolve b1e743 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e743
        have b1e759 : y = (M.op x x) := by
          first
          | (have i₁ := b1e742
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e742
          | exact resolve b1e742 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e742
        have b1e761 : ∀ X0 : G, (σ (M.op (M.op x x) X0)) = (σ (k y X0)) := by
          intro X0
          first
          | (have i₁ := b1e758 X0
             have i₂ := b1e422 x X0
             grind)
          | exact superpose b1e422 b1e758
          | exact resolve b1e758 b1e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e422 b1e758
        have b1e763 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) := by
          intro X0
          first
          | (have i₁ := b1e761 X0
             have i₂ := b1e759
             grind)
          | exact superpose b1e759 b1e761
          | exact resolve b1e761 b1e759
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e759 b1e761
        have b1e845 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b1e513 (σ x) (σ y)
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e513
          | exact resolve b1e513 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e513
        have b1e855 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e845
             have i₂ := b1e18 y x
             grind)
          | exact superpose b1e18 b1e845
          | exact resolve b1e845 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e845
        have b1e862 : (M.op (σ x) (σ y)) = (σ (M.op y x)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e855
             have i₂ := b1e763 x
             grind)
          | exact superpose b1e763 b1e855
          | exact resolve b1e855 b1e763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e855
        have b1e867 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e862
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e862
          | exact resolve b1e862 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e862
        have b1e868 : (σ y) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b1e867
             have r₂ := b1e82
             grind)
          | exact resolve b1e867 b1e82
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e82 b1e867
        have b1e3635 : (σ x) ≠ (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e161 y x
             grind)
          | exact superpose b1e161 b1e21
          | (have j1 := b1e161 y x
             grind)
          | exact resolve b1e21 b1e161
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e161
        have b1e3689 : (σ x) ≠ (σ (M.op y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e3635
             have i₂ := b1e763 x
             grind)
          | exact superpose b1e763 b1e3635
          | exact resolve b1e3635 b1e763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3635
        have b1e3712 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b1e3689
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e3689
          | exact resolve b1e3689 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3689
        have b1e3713 : (σ y) = (σ (k y x)) := by grind
        clear b1e3712
        have b1e3730 : (σ y) = (σ (M.op y x)) := by
          first
          | (have i₁ := b1e3713
             have i₂ := b1e763 x
             grind)
          | exact superpose b1e763 b1e3713
          | exact resolve b1e3713 b1e763
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e763 b1e3713
        have b1e3737 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e3730
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e3730
          | exact resolve b1e3730 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3730
        have b1e3752 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e868
             have i₂ := b1e3737
             grind)
          | exact superpose b1e3737 b1e868
          | exact resolve b1e868 b1e3737
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e868
        have b1e3795 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e3752
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e3752
          | exact resolve b1e3752 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e3752
        have b1e3811 : False := by grind
        exact b1e3811
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : x = (M.op y x) := by grind
        have b2e22 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e32 : x ≠ x ∨ (M.op x y) = (k x y) := by
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
        have b2e35 : (M.op x y) = (k x y) := by grind
        clear b2e32
        have b2e55 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e57 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e55 X0
             have j1 := b2e15 (σ x) X0
             grind)
          | (have r₁ := b2e55 x
             have r₂ := b2e15 (σ x) x
             grind)
          | exact resolve b2e55 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e55
        have b2e128 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e57 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e57
        have b2e129 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e128
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e128
          | exact resolve b2e128 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e128
        have b2e130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e129
             have i₂ := b2e35
             grind)
          | exact superpose b2e35 b2e129
          | exact resolve b2e129 b2e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e35 b2e129
        have b2e131 : False := by grind
        exact b2e131
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X1) := by
          intro X0 X1
          grind
        have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : x ≠ (M.op y x) := by grind
        have b3e21 : y = (M.op x x) := by grind
        have b3e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e26 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 (M.op X1 X1) X1
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e27 : (M.op x y) = (M.op y x) := by
          first
          | (have i₁ := b3e12 x x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e29 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1
             have i₂ := b3e12 X2 X1
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e30 : x ≠ (M.op x y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e27
             grind)
          | exact superpose b3e27 b3e20
          | exact resolve b3e20 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27
        have b3e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 (M.op X1 X1)) = (k X1 (M.op X1 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 (M.op X1 X1)
             have i₂ := b3e12 X0 X1
             grind)
          | exact superpose b3e12 b3e15
          | (have j0 := b3e15 X1 (M.op X1 X1)
             grind)
          | (have r₁ := b3e15 (M.op (M.op X1 X1) X1) (M.op X1 X1)
             have r₂ := b3e12 (M.op X1 X1) X1
             grind)
          | exact resolve b3e15 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e33 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e36 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e33
        have b3e37 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e36
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e36
          | exact resolve b3e36 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e36
        have b3e38 : x = (k x y) ∨ x = (M.op y x) := by grind
        have b3e39 : x = (k x y) := by
          first
          | (have r₁ := b3e38
             have r₂ := b3e20
             grind)
          | exact resolve b3e38 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e42 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e17 X1 X2
             have i₂ := b3e17 X1 X0
             grind)
          | (have i₁ := b3e17 X0 X1
             have i₂ := b3e17 X0 (M.op X0 X0)
             grind)
          | exact superpose b3e17 b3e17
          | (have j0 := b3e17 X1 X2
             have j1 := b3e17 X1 X2
             grind)
          | exact resolve b3e17 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e46 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2
             have i₂ := b3e17 X2 X0
             grind)
          | (have i₁ := b3e12 X0 X1
             have i₂ := b3e17 X0 (M.op X1 X1)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X2 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e49 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e45 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e45
        have b3e52 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e46 X0 X1 X2
             have j1 := b3e15 X2 X0
             grind)
          | (have r₁ := b3e46 X1 X1 X2
             have r₂ := b3e15 (M.op X1 X2) X1
             grind)
          | (have r₁ := b3e46 X1 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e46 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e53 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e49 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e49 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e49 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e54 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1 X2
          first
          | (have j0 := b3e42 X0 X1 X2
             have j1 := b3e15 X1 X2
             grind)
          | (have r₁ := b3e42 (M.op X1 X0) X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e42 X0 X1 (M.op X1 X0)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e42 X0 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e42 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e55 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1 X2
          first
          | (have j0 := b3e54 X0 X1 X2
             have j1 := b3e15 X1 X2
             grind)
          | (have r₁ := b3e54 (M.op X1 X0) X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e54 X0 X1 (M.op X1 X0)
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e54 X1 X0 X2
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e54 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e82 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e37
             grind)
          | exact superpose b3e37 b3e19
          | exact resolve b3e19 b3e37
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e37
        have b3e85 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e39
             grind)
          | exact superpose b3e39 b3e82
          | exact resolve b3e82 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e82
        have b3e109 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e29 X0 (σ x) (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e29
          | exact resolve b3e29 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29
        have b3e127 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b3e109 X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e109
          | exact resolve b3e109 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e109
        have b3e201 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e26 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e26 X0 X1
             have i₂ := b3e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b3e17 b3e26
          | (have j1 := b3e17 X1 X0
             grind)
          | exact resolve b3e26 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e26
        have b3e237 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e201 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e201 X1 X1
             have r₂ := b3e15 (M.op X1 X1) X1
             grind)
          | (have r₁ := b3e201 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e201 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e201
        have b3e325 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b3e127 x
             have i₂ := b3e52 X0 x (σ x)
             grind)
          | exact superpose b3e52 b3e127
          | (have j1 := b3e52 X0 x (σ x)
             grind)
          | exact resolve b3e127 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e370 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
          intro X0
          first
          | (have j0 := b3e325 X0
             have j1 := b3e15 (σ x) X0
             grind)
          | (have r₁ := b3e325 x
             have r₂ := b3e15 (σ x) x
             grind)
          | exact resolve b3e325 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e325
        have b3e419 : ∀ X0 : G, x = (M.op x y) ∨ y = X0 ∨ (M.op x X0) = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e39
             have i₂ := b3e55 y x X0
             grind)
          | exact superpose b3e55 b3e39
          | (have j1 := b3e55 y x X0
             grind)
          | exact resolve b3e39 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e55
        have b3e422 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
          intro X0
          first
          | (have j0 := b3e419 X0
             grind)
          | (have r₁ := b3e419 X0
             have r₂ := b3e30
             grind)
          | exact resolve b3e419 b3e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e30 b3e419
        have b3e432 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 x X0
             have i₂ := b3e370 (σ X0)
             grind)
          | exact superpose b3e370 b3e18
          | exact resolve b3e18 b3e370
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e370
        have b3e446 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have i₁ := b3e32 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e32 X0 X1
             have i₂ := b3e17 X0 (M.op X0 X1)
             grind)
          | exact superpose b3e17 b3e32
          | (have j1 := b3e17 X1 X0
             grind)
          | (have r₁ := b3e32 X0 (M.op X0 X0)
             have r₂ := b3e17 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
             grind)
          | exact resolve b3e32 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e32
        have b3e465 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          first
          | (have j0 := b3e446 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e446
        have b3e470 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e465 X0 X1
             have j1 := b3e15 X1 X0
             grind)
          | (have r₁ := b3e465 X1 X0
             have r₂ := b3e15 X0 X1
             grind)
          | exact resolve b3e465 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e465
        have b3e684 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ (k x x)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b3e12 X0 (σ x)
             have i₂ := b3e432 x
             grind)
          | exact superpose b3e432 b3e12
          | exact resolve b3e12 b3e432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e699 : (σ x) = (M.op (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b3e684 x
             have i₂ := b3e127 x
             grind)
          | exact superpose b3e127 b3e684
          | exact resolve b3e684 b3e127
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e127 b3e684
        have b3e1024 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (k (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b3e470 (σ x) (σ (k x x))
             have i₂ := b3e699
             grind)
          | exact superpose b3e699 b3e470
          | exact resolve b3e470 b3e699
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e470
        have b3e1027 : (σ x) = (σ (k (k x x) x)) ∨ (σ x) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b3e1024
             have i₂ := b3e18 (k x x) x
             grind)
          | exact superpose b3e18 b3e1024
          | exact resolve b3e1024 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1024
        have b3e2792 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b3e237 (σ x) (σ (k x x))
             have i₂ := b3e699
             grind)
          | exact superpose b3e699 b3e237
          | exact resolve b3e237 b3e699
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e237 b3e699
        have b3e2878 : (σ x) = (σ (k x x)) ∨ (σ x) = (k (σ (k x x)) (σ x)) := by
          first
          | (have i₁ := b3e2792
             have i₂ := b3e432 x
             grind)
          | exact superpose b3e432 b3e2792
          | exact resolve b3e2792 b3e432
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e432 b3e2792
        have b3e2888 : (σ x) = (σ (k (k x x) x)) ∨ (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b3e2878
             have i₂ := b3e18 (k x x) x
             grind)
          | exact superpose b3e18 b3e2878
          | exact resolve b3e2878 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2878
        have b3e2895 : (σ x) = (σ (k (k x x) x)) := by
          first
          | (have r₁ := b3e2888
             have r₂ := b3e1027
             grind)
          | exact resolve b3e2888 b3e1027
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1027 b3e2888
        have b3e2906 : (τ (σ x)) = (k (k x x) x) := by
          first
          | (have i₁ := b3e13 (k (k x x) x)
             have i₂ := b3e2895
             grind)
          | exact superpose b3e2895 b3e13
          | exact resolve b3e13 b3e2895
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2895
        have b3e2946 : x = (k (k x x) x) := by
          first
          | (have i₁ := b3e2906
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e2906
          | exact resolve b3e2906 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e2906
        have b3e3140 : x = (k (M.op x x) x) ∨ x = y := by
          first
          | (have i₁ := b3e2946
             have i₂ := b3e422 x
             grind)
          | exact superpose b3e422 b3e2946
          | (have j1 := b3e422 x
             grind)
          | exact resolve b3e2946 b3e422
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e422 b3e2946
        have b3e3159 : x = (k y x) ∨ x = y := by
          first
          | (have i₁ := b3e3140
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3140
          | exact resolve b3e3140 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3140
        have b3e3273 : x = (M.op y x) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b3e53 x y
             have i₂ := b3e3159
             grind)
          | exact superpose b3e3159 b3e53
          | exact resolve b3e53 b3e3159
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e3159
        have b3e3276 : x = (M.op y x) ∨ x = y := by grind
        clear b3e3273
        have b3e3279 : x = y := by
          first
          | (have r₁ := b3e3276
             have r₂ := b3e20
             grind)
          | exact resolve b3e3276 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3276
        have b3e3390 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e85
             have i₂ := b3e3279
             grind)
          | exact superpose b3e3279 b3e85
          | exact resolve b3e85 b3e3279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e85
        have b3e3416 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b3e3390
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e3390
          | exact resolve b3e3390 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3390
        have b3e3431 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e3416
             have i₂ := b3e3279
             grind)
          | exact superpose b3e3279 b3e3416
          | exact resolve b3e3416 b3e3279
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e3279 b3e3416
        have b3e3432 : False := by grind
        exact b3e3432
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X1) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
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
          have b4e31 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e14 (k (τ X0) X1)
               have i₂ := b4e26 X0 X1
               grind)
            | exact superpose b4e26 b4e14
            | exact resolve b4e14 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (M.op X1 X1) X1
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e13 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e34 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (M.op X0 (σ x))) := by
            intro X0
            first
            | (have i₁ := b4e13 X0 (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e13 X2 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e41 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b4e16 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e16
            | exact resolve b4e16 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b4e41
               have i₂ := b4e19 x x
               grind)
            | exact superpose b4e19 b4e41
            | exact resolve b4e41 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e47 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            grind
          have b4e48 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e47 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e47
            | (have j0 := b4e47 X0
               grind)
            | exact resolve b4e47 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e54 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e18 X1 X2
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e18 X0 X1
               have i₂ := b4e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b4e18 b4e18
            | (have j0 := b4e18 X1 X2
               have j1 := b4e18 X1 X2
               grind)
            | exact resolve b4e18 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b4e59 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e60 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2
               have i₂ := b4e18 X2 X0
               grind)
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e18 b4e13
            | (have j1 := b4e18 X2 X0
               grind)
            | exact resolve b4e13 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e61 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e16 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 (M.op X1 X0)
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X1 X0
               have j1 := b4e18 X1 X0
               grind)
            | (have r₁ := b4e16 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 (M.op X0 X0) X1
               have r₂ := b4e18 X0 (M.op X1 (M.op X0 X0))
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e64 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e59 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59
          have b4e67 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X1 X1) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e61 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e61 (M.op X0 X1) (k X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e61 (k X0 X1) (M.op X0 X1)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e61 (M.op X1 (k X1 X1)) X1
               have r₂ := b4e16 (k X1 X1) X1
               grind)
            | exact resolve b4e61 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e61
          have b4e68 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op X0 X2) ∨ (M.op X2 X0) = (k X2 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e60 X0 X1 X2
               have j1 := b4e16 X2 X0
               grind)
            | (have r₁ := b4e60 X1 X1 X2
               have r₂ := b4e16 (M.op X1 X2) X1
               grind)
            | (have r₁ := b4e60 X1 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e60 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e60
          have b4e69 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e64 X0 X1
               have j1 := b4e16 X1 X0
               grind)
            | (have r₁ := b4e64 X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e64 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e64
          have b4e71 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b4e54 X0 X1 X2
               have j1 := b4e16 X1 X2
               grind)
            | (have r₁ := b4e54 (M.op X1 X0) X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e54 X0 X1 (M.op X1 X0)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e54 X0 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e54 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e72 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e71 X0 X1 X2
               have j1 := b4e16 X1 X2
               grind)
            | (have r₁ := b4e71 (M.op X1 X0) X1 X0
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e71 X0 X1 (M.op X1 X0)
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e71 X1 X0 X2
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e71 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e71
          have b4e89 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
          have b4e92 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e31 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e31
            | exact resolve b4e31 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e101 : (σ x) ≠ (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e23
               have i₂ := b4e33
               grind)
            | exact superpose b4e33 b4e23
            | exact resolve b4e23 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e126 : ∀ X0 : G, (M.op X0 (M.op X0 (σ x))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            intro X0
            first
            | (have i₁ := b4e37 X0 (σ x) (σ y)
               have i₂ := b4e33
               grind)
            | exact superpose b4e33 b4e37
            | exact resolve b4e37 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e127 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e37 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e142 : (M.op (σ y) (σ x)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e126 x
               have i₂ := b4e35 x
               grind)
            | exact superpose b4e35 b4e126
            | exact resolve b4e126 b4e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35 b4e126
          have b4e150 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b4e142
               have i₂ := b4e33
               grind)
            | exact superpose b4e33 b4e142
            | exact resolve b4e142 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e142
          have b4e218 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e27 X1 X0
               have i₂ := b4e69 (τ X1) X0
               grind)
            | exact superpose b4e69 b4e27
            | (have j1 := b4e69 (τ X1) X0
               grind)
            | exact resolve b4e27 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e224 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e69 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69
          have b4e229 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) ≠ X1 ∨ (k X1 (M.op X1 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e224 X1 (M.op X1 X0)
               have i₂ := b4e13 X1 X0
               grind)
            | exact superpose b4e13 b4e224
            | (have j0 := b4e224 X1 (M.op X1 X0)
               grind)
            | (have r₁ := b4e224 (M.op (M.op X1 X1) X1) (M.op (M.op (M.op X1 X1) X1) X1)
               have r₂ := b4e13 (M.op (M.op X1 X1) X1) X1
               grind)
            | exact resolve b4e224 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e224
          have b4e352 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e68 X2 (M.op X1 X1) (M.op X0 (M.op X0 X1))
               have i₂ := b4e32 X0 X1
               grind)
            | exact superpose b4e32 b4e68
            | (have j0 := b4e68 X2 X1 (M.op X0 (M.op X0 X1))
               grind)
            | exact resolve b4e68 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e404 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X1 X2
               have i₂ := b4e68 X2 X0 X1
               grind)
            | exact superpose b4e68 b4e16
            | (have j0 := b4e16 X1 X2
               have j1 := b4e68 X2 X1 X1
               grind)
            | (have r₁ := b4e16 (M.op X0 X2) X0
               have r₂ := b4e68 X0 X0 X2
               grind)
            | exact resolve b4e16 b4e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e429 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 X2) = (k X1 X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e404 X0 X1 X2
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e404
          have b4e456 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op (M.op X0 (M.op X0 X1)) X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e352 X0 X1 X2
               have i₂ := b4e32 X0 X1
               grind)
            | exact superpose b4e32 b4e352
            | (have j0 := b4e352 X0 X1 X2
               grind)
            | exact resolve b4e352 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32 b4e352
          have b4e475 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) X2) = (k (M.op X0 (M.op X0 X1)) X2) := by
            intro X0 X1 X2
            first
            | (have j0 := b4e456 X0 X1 X2
               have j1 := b4e16 (M.op X0 (M.op X0 X1)) X2
               grind)
            | (have r₁ := b4e456 X0 X1 X1
               have r₂ := b4e16 (M.op X0 (M.op X0 X1)) X1
               grind)
            | exact resolve b4e456 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e456
          have b4e517 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          clear b4e72
          have b4e528 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e517 X0 X1
               have j1 := b4e429 X0 X0 X1
               grind)
            | (have r₁ := b4e517 X1 X1
               have r₂ := b4e429 X1 X1 x
               grind)
            | (have r₁ := b4e517 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
               have r₂ := b4e429 X0 (M.op X0 X0) x
               grind)
            | exact resolve b4e517 b4e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e517
          have b4e654 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e56 x x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e56
            | exact resolve b4e56 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e658 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e56 X1 X1
               have i₂ := b4e18 (σ X1) X1
               grind)
            | (have i₁ := b4e56 X0 X1
               have i₂ := b4e18 X0 (M.op (σ X1) (σ X0))
               grind)
            | exact superpose b4e18 b4e56
            | (have j1 := b4e18 (σ X1) X0
               grind)
            | exact resolve b4e56 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e706 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X0) (σ X1)
               have i₂ := b4e56 X0 X1
               grind)
            | exact superpose b4e56 b4e16
            | (have j0 := b4e16 (σ X0) (σ X1)
               have j1 := b4e56 X0 X1
               grind)
            | (have r₁ := b4e16 (σ X1) (σ X1)
               have r₂ := b4e56 X1 X1
               grind)
            | (have r₁ := b4e16 (σ X0) (σ X1)
               have r₂ := b4e56 X0 X1
               grind)
            | exact resolve b4e16 b4e56
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e719 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e706 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e706
          have b4e728 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e658 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e658
          have b4e730 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
          clear b4e654
          have b4e738 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e719 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e719
            | (have j0 := b4e719 X0 X1
               grind)
            | exact resolve b4e719 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e719
          have b4e739 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
            intro X0 X1
            first
            | (have j0 := b4e738 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e738
          have b4e759 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e728 X0 X1
               have j1 := b4e16 (σ X1) X0
               grind)
            | (have r₁ := b4e728 (M.op X1 (σ X1)) X1
               have r₂ := b4e16 (σ X1) X1
               grind)
            | (have r₁ := b4e728 (M.op X1 (σ (k X1 X1))) X1
               have r₂ := b4e16 (σ (k X1 X1)) X1
               grind)
            | (have r₁ := b4e728 X1 X1
               have r₂ := b4e16 (σ X1) X1
               grind)
            | exact resolve b4e728 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e728
          have b4e760 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b4e730
               have r₂ := b4e44
               grind)
            | exact resolve b4e730 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e730
          have b4e786 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b4e14 (k x x)
               have i₂ := b4e760
               grind)
            | exact superpose b4e760 b4e14
            | exact resolve b4e14 b4e760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e787 : ∀ X0 : G, (σ (k (k x x) X0)) = (k (σ y) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 (k x x) X0
               have i₂ := b4e760
               grind)
            | exact superpose b4e760 b4e19
            | exact resolve b4e19 b4e760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e788 : ∀ X0 : G, (σ (k X0 (k x x))) = (k (σ X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 (k x x)
               have i₂ := b4e760
               grind)
            | exact superpose b4e760 b4e19
            | exact resolve b4e19 b4e760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e795 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b4e89 (k x x) X0
               have i₂ := b4e760
               grind)
            | exact superpose b4e760 b4e89
            | exact resolve b4e89 b4e760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e797 : ∀ X0 : G, (k (k x x) (τ X0)) = (k y (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e795 X0
               have i₂ := b4e89 y X0
               grind)
            | exact superpose b4e89 b4e795
            | exact resolve b4e795 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e795
          have b4e799 : ∀ X0 : G, (σ (k X0 (k x x))) = (σ (k X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e788 X0
               have i₂ := b4e19 X0 y
               grind)
            | exact superpose b4e19 b4e788
            | exact resolve b4e788 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e788
          have b4e800 : ∀ X0 : G, (σ (k (k x x) X0)) = (σ (k y X0)) := by
            intro X0
            first
            | (have i₁ := b4e787 X0
               have i₂ := b4e19 y X0
               grind)
            | exact superpose b4e19 b4e787
            | exact resolve b4e787 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e787
          have b4e801 : y = (k x x) := by
            first
            | (have i₁ := b4e786
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e786
            | exact resolve b4e786 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e786
          have b4e1044 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e68 X0 (σ y) (M.op (σ x) (σ y))
               have i₂ := b4e150
               grind)
            | exact superpose b4e150 b4e68
            | (have j0 := b4e68 X0 x (M.op (σ x) (σ y))
               grind)
            | exact resolve b4e68 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e68
          have b4e1048 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e1044 X0
               have i₂ := b4e150
               grind)
            | exact superpose b4e150 b4e1044
            | (have j0 := b4e1044 X0
               grind)
            | exact resolve b4e1044 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1044
          have b4e1053 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k (M.op (σ x) (σ y)) X0) := by
            intro X0
            first
            | (have j0 := b4e1048 X0
               have j1 := b4e16 (M.op (σ x) (σ y)) X0
               grind)
            | (have r₁ := b4e1048 x
               have r₂ := b4e16 (M.op (σ x) (σ y)) x
               grind)
            | exact resolve b4e1048 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1048
          have b4e1144 : ∀ X0 X2 : G, (M.op (M.op X0 X0) X0) ≠ X0 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e429 x X0 X2
               have i₂ := b4e13 x X0
               grind)
            | exact superpose b4e13 b4e429
            | (have j0 := b4e429 X0 X0 X2
               grind)
            | exact resolve b4e429 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e3282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e218 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e218
            | exact resolve b4e218 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e218
          have b4e3322 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e3282 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e3282
            | (have j0 := b4e3282 X0 X1
               grind)
            | exact resolve b4e3282 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3282
          have b4e5993 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X0
               have i₂ := b4e528 X0 X2
               grind)
            | exact superpose b4e528 b4e13
            | (have j1 := b4e528 X0 X2
               grind)
            | exact resolve b4e13 b4e528
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e528
          have b4e6173 : ∀ X0 X2 : G, (M.op X0 X0) = X2 ∨ (M.op X0 X2) = (k X0 X2) := by
            intro X0 X2
            first
            | (have j0 := b4e5993 X0 x X2
               have j1 := b4e429 X0 X0 X2
               grind)
            | (have r₁ := b4e5993 x X0 X2
               have r₂ := b4e429 X0 x X2
               grind)
            | (have r₁ := b4e5993 X0 x (M.op X0 (M.op X0 (M.op X0 X0)))
               have r₂ := b4e429 X0 (M.op X0 X0) X2
               grind)
            | exact resolve b4e5993 b4e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5993
          have b4e6326 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op (k x x) X0)) ∨ (M.op (k x x) (k x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e800 X0
               have i₂ := b4e6173 (k x x) X0
               grind)
            | exact superpose b4e6173 b4e800
            | (have j1 := b4e6173 (k x x) X0
               grind)
            | exact resolve b4e800 b4e6173
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6173
          have b4e6345 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op (k x x) (k x x)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e6326 X0
               have i₂ := b4e801
               grind)
            | exact superpose b4e801 b4e6326
            | (have j0 := b4e6326 X0
               grind)
            | exact resolve b4e6326 b4e801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6326
          have b4e6361 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op y X0)) ∨ (M.op y y) = X0 := by
            intro X0
            first
            | (have i₁ := b4e6345 X0
               have i₂ := b4e801
               grind)
            | exact superpose b4e801 b4e6345
            | (have j0 := b4e6345 X0
               grind)
            | exact resolve b4e6345 b4e801
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e801 b4e6345
          have b4e6379 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (σ (k (τ X0) (τ X0))) = X1 ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e759 X0 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e759
            | (have j0 := b4e759 X1 (τ X0)
               grind)
            | exact resolve b4e759 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e759
          have b4e6502 : ∀ X0 X1 : G, (k (σ (τ X0)) X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e6379 X0 X1
               have i₂ := b4e27 X0 (τ X0)
               grind)
            | exact superpose b4e27 b4e6379
            | (have j0 := b4e6379 X0 X1
               grind)
            | exact resolve b4e6379 b4e27
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6379
          have b4e6518 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e6502 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e6502
            | (have j0 := b4e6502 X0 X1
               grind)
            | exact resolve b4e6502 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6502
          have b4e6529 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e6518 X0 X1
               have j1 := b4e67 X1 X0
               grind)
            | (have r₁ := b4e6518 X0 X1
               have r₂ := b4e67 (k X0 X0) X1
               grind)
            | (have r₁ := b4e6518 X0 X0
               have r₂ := b4e67 X0 (k X0 X0)
               grind)
            | (have r₁ := b4e6518 X0 X1
               have r₂ := b4e67 (M.op X0 X1) (k X0 X1)
               grind)
            | exact resolve b4e6518 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67 b4e6518
          have b4e6607 : ∀ X0 X1 : G, (σ X0) = (k X1 (σ (τ X1))) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e26 X1 (τ X1)
               have i₂ := b4e6529 (τ X1) X0
               grind)
            | (have i₁ := b4e26 X0 X1
               have i₂ := b4e6529 X0 (k (τ X0) X1)
               grind)
            | exact superpose b4e6529 b4e26
            | (have j1 := b4e6529 (τ X1) X0
               grind)
            | exact resolve b4e26 b4e6529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6627 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 ∨ (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            grind
          have b4e6642 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) ∨ (k (σ X0) (σ X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e89 X0 X1
               have i₂ := b4e6529 (σ X0) X1
               grind)
            | exact superpose b4e6529 b4e89
            | (have j1 := b4e6529 (σ X0) X1
               grind)
            | exact resolve b4e89 b4e6529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6671 : ∀ X0 X1 : G, (σ (k X0 X0)) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e6642 X0 X1
               have i₂ := b4e19 X0 X0
               grind)
            | exact superpose b4e19 b4e6642
            | (have j0 := b4e6642 X0 X1
               grind)
            | exact resolve b4e6642 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6642
          have b4e6678 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e6627 X0
               have j1 := b4e429 X0 X0 X0
               grind)
            | (have r₁ := b4e6627 x
               have r₂ := b4e429 x x x
               grind)
            | exact resolve b4e6627 b4e429
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e429 b4e6627
          have b4e6684 : ∀ X0 X1 : G, (σ X0) = (k X1 X1) ∨ (M.op (τ X1) X0) = (k (τ X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e6607 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e6607
            | (have j0 := b4e6607 X0 X1
               grind)
            | exact resolve b4e6607 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6607
          have b4e6710 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e6678 X0
               have j1 := b4e1144 X0 X0
               grind)
            | (have r₁ := b4e6678 X0
               have r₂ := b4e1144 X0 x
               grind)
            | exact resolve b4e6678 b4e1144
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1144 b4e6678
          have b4e6883 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e6710 (σ X0)
               grind)
            | exact superpose b4e6710 b4e19
            | exact resolve b4e19 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6889 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e92 X0 X0
               have i₂ := b4e6710 (τ X0)
               grind)
            | exact superpose b4e6710 b4e92
            | exact resolve b4e92 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e6904 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e6889 X0
               have i₂ := b4e6710 X0
               grind)
            | exact superpose b4e6710 b4e6889
            | exact resolve b4e6889 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6889
          have b4e6910 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e6883 X0
               have i₂ := b4e6710 X0
               grind)
            | exact superpose b4e6710 b4e6883
            | exact resolve b4e6883 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6883
          have b4e10326 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (M.op (τ X0) (τ X0)) (τ X0)) := by
            intro X0
            first
            | (have i₁ := b4e31 X0 (M.op (τ X0) (τ X0))
               have i₂ := b4e48 X0
               grind)
            | exact superpose b4e48 b4e31
            | (have j1 := b4e48 X0
               grind)
            | exact resolve b4e31 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e10404 : ∀ X0 : G, (τ X0) = (k (τ X0) (M.op (τ X0) (τ X0))) := by
            intro X0
            first
            | (have j0 := b4e10326 X0
               have j1 := b4e229 (τ X0) (τ X0)
               grind)
            | (have r₁ := b4e10326 X0
               have r₂ := b4e229 (τ X0) (τ X0)
               grind)
            | exact resolve b4e10326 b4e229
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e229 b4e10326
          have b4e10494 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e10404 X0
               have i₂ := b4e6904 X0
               grind)
            | exact superpose b4e6904 b4e10404
            | exact resolve b4e10404 b4e6904
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6904 b4e10404
          have b4e10572 : ∀ X0 : G, (τ X0) = (τ (k X0 (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e10494 X0
               have i₂ := b4e92 (M.op X0 X0) X0
               grind)
            | exact superpose b4e92 b4e10494
            | exact resolve b4e10494 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10494
          have b4e10804 : ∀ X0 X1 : G, (τ (σ X1)) = (τ (k (σ X1) (σ X0))) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e10572 (σ X1)
               have i₂ := b4e739 X1 X0
               grind)
            | exact superpose b4e739 b4e10572
            | (have j1 := b4e739 X1 X0
               grind)
            | exact resolve b4e10572 b4e739
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e739
          have b4e10841 : ∀ X0 : G, (σ (τ X0)) = (k X0 (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e15 (k X0 (M.op X0 X0))
               have i₂ := b4e10572 X0
               grind)
            | exact superpose b4e10572 b4e15
            | exact resolve b4e15 b4e10572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e10845 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 (k X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e92 (k X0 (M.op X0 X0)) X1
               have i₂ := b4e10572 X0
               grind)
            | exact superpose b4e10572 b4e92
            | exact resolve b4e92 b4e10572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e10846 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k (k X0 (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e92 X1 (k X0 (M.op X0 X0))
               have i₂ := b4e10572 X0
               grind)
            | exact superpose b4e10572 b4e92
            | exact resolve b4e92 b4e10572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10572
          have b4e10862 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (k (k X0 (M.op X0 X0)) X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e10846 X0 X1
               have i₂ := b4e92 X1 X0
               grind)
            | exact superpose b4e92 b4e10846
            | exact resolve b4e10846 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10846
          have b4e10863 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (k X1 (k X0 (M.op X0 X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e10845 X0 X1
               have i₂ := b4e92 X0 X1
               grind)
            | exact superpose b4e92 b4e10845
            | exact resolve b4e10845 b4e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e92 b4e10845
          have b4e10867 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
            intro X0
            first
            | (have i₁ := b4e10841 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e10841
            | exact resolve b4e10841 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10841
          have b4e10888 : ∀ X0 X1 : G, (τ (σ X1)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e10804 X0 X1
               have i₂ := b4e31 (σ X1) X0
               grind)
            | exact superpose b4e31 b4e10804
            | (have j0 := b4e10804 X0 X1
               grind)
            | exact resolve b4e10804 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e10804
          have b4e10916 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e10888 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e10888
            | (have j0 := b4e10888 X0 X1
               grind)
            | exact resolve b4e10888 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10888
          have b4e12129 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 (k X1 (M.op X1 X1)))) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e10862 X1 (k X1 (M.op X1 X1))
               have i₂ := b4e6529 (k X1 (M.op X1 X1)) X0
               grind)
            | (have i₁ := b4e10862 X0 X1
               have i₂ := b4e6529 X0 (k (k X0 (M.op X0 X0)) X1)
               grind)
            | exact superpose b4e6529 b4e10862
            | (have j1 := b4e6529 (k X1 (M.op X1 X1)) X0
               grind)
            | exact resolve b4e10862 b4e6529
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6529 b4e10862
          have b4e12221 : ∀ X0 X1 : G, (τ X0) = (τ (k X1 X1)) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e12129 X0 X1
               have i₂ := b4e10863 X1 X1
               grind)
            | exact superpose b4e10863 b4e12129
            | (have j0 := b4e12129 X0 X1
               grind)
            | exact resolve b4e12129 b4e10863
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10863 b4e12129
          have b4e12268 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X1 X1)) ∨ (M.op (k X1 (M.op X1 X1)) X0) = (k (k X1 (M.op X1 X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e12221 X0 X1
               have i₂ := b4e6710 X1
               grind)
            | exact superpose b4e6710 b4e12221
            | (have j0 := b4e12221 X0 X1
               grind)
            | exact resolve b4e12221 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12221
          have b4e12303 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (τ X0) = (τ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e12268 X0 X0
               have i₂ := b4e10867 X0
               grind)
            | exact superpose b4e10867 b4e12268
            | (have j0 := b4e12268 X0 X1
               grind)
            | exact resolve b4e12268 b4e10867
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10867 b4e12268
          have b4e21134 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X1)) = (τ (M.op (σ X0) (σ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X0 X1
               have i₂ := b4e12303 (σ X1) (σ X0)
               grind)
            | exact superpose b4e12303 b4e19
            | (have j1 := b4e12303 (σ X1) (σ X0)
               grind)
            | exact resolve b4e19 b4e12303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e12303
          have b4e21270 : ∀ X0 X1 : G, (τ (σ X1)) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21134 X0 X1
               have i₂ := b4e6910 X0
               grind)
            | exact superpose b4e6910 b4e21134
            | (have j0 := b4e21134 X0 X1
               grind)
            | exact resolve b4e21134 b4e6910
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6910 b4e21134
          have b4e21324 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21270 X0 X1
               have i₂ := b4e14 (M.op X0 X0)
               grind)
            | exact superpose b4e14 b4e21270
            | (have j0 := b4e21270 X0 X1
               grind)
            | exact resolve b4e21270 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21270
          have b4e21344 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e21324 X0 X1
               have i₂ := b4e14 X1
               grind)
            | exact superpose b4e14 b4e21324
            | (have j0 := b4e21324 X0 X1
               grind)
            | exact resolve b4e21324 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21324
          have b4e93291 : ∀ X0 X1 : G, (σ X0) = (σ (k X1 X1)) ∨ (k (τ (σ X1)) X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X1
               have i₂ := b4e6684 X0 (σ X1)
               grind)
            | exact superpose b4e6684 b4e19
            | (have j1 := b4e6684 X0 (σ X1)
               grind)
            | exact resolve b4e19 b4e6684
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6684
          have b4e93421 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (k (τ (σ X1)) X0) = (M.op (τ (σ X1)) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e93291 X0 X1
               have i₂ := b4e6710 X1
               grind)
            | exact superpose b4e6710 b4e93291
            | (have j0 := b4e93291 X0 X1
               grind)
            | exact resolve b4e93291 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93291
          have b4e93775 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (σ X0) = (σ (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e93421 X0 X0
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e93421
            | (have j0 := b4e93421 X0 X1
               grind)
            | exact resolve b4e93421 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93421
          have b4e104016 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e10916 x y
               grind)
            | exact superpose b4e10916 b4e33
            | (have j1 := b4e10916 x y
               grind)
            | exact resolve b4e33 b4e10916
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e10916
          have b4e172614 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e104016
               grind)
            | exact superpose b4e104016 b4e20
            | exact resolve b4e20 b4e104016
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104016
          have b4e173015 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e172614
               have i₂ := b4e3322 x y
               grind)
            | exact superpose b4e3322 b4e172614
            | (have j1 := b4e3322 x y
               grind)
            | exact resolve b4e172614 b4e3322
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3322 b4e172614
          have b4e173024 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (k y x) := by grind
          clear b4e173015
          have b4e173030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k y x) := by
            first
            | (have i₁ := b4e173024
               have i₂ := b4e34
               grind)
            | exact superpose b4e34 b4e173024
            | exact resolve b4e173024 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173024
          have b4e173031 : y = (k y x) := by grind
          clear b4e173030
          have b4e173356 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e6361 x
               have i₂ := b4e173031
               grind)
            | exact superpose b4e173031 b4e6361
            | (have j0 := b4e6361 x
               grind)
            | exact resolve b4e6361 b4e173031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6361
          have b4e173386 : (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e173356
               have i₂ := b4e34
               grind)
            | exact superpose b4e34 b4e173356
            | exact resolve b4e173356 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e173356
          have b4e187908 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e21344 y x
               grind)
            | exact superpose b4e21344 b4e33
            | (have j1 := b4e21344 y x
               grind)
            | exact resolve b4e33 b4e21344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e21344
          have b4e188261 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e187908
               have i₂ := b4e173031
               grind)
            | exact superpose b4e173031 b4e187908
            | exact resolve b4e187908 b4e173031
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173031 b4e187908
          have b4e194191 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e188261
               grind)
            | exact superpose b4e188261 b4e20
            | exact resolve b4e20 b4e188261
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e188261
          have b4e194375 : x = (M.op y y) := by
            first
            | (have r₁ := b4e194191
               have r₂ := b4e173386
               grind)
            | exact resolve b4e194191 b4e173386
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e173386 b4e194191
          have b4e195741 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (σ X0) = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e93775 X0 y
               have i₂ := b4e194375
               grind)
            | exact superpose b4e194375 b4e93775
            | (have j0 := b4e93775 X0 y
               grind)
            | exact resolve b4e93775 b4e194375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e93775
          have b4e205723 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (σ (τ X0)) = (σ x) := by
            intro X0
            first
            | (have i₁ := b4e27 X0 y
               have i₂ := b4e195741 (τ X0)
               grind)
            | exact superpose b4e195741 b4e27
            | (have j1 := b4e195741 (τ X0)
               grind)
            | exact resolve b4e27 b4e195741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e27 b4e195741
          have b4e205734 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op y (τ X0))) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e205723 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e205723
            | (have j0 := b4e205723 X0
               grind)
            | exact resolve b4e205723 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e205723
          have b4e221333 : ∀ X0 : G, (τ (k (σ y) X0)) = (M.op y (τ X0)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e14 (M.op y (τ X0))
               have i₂ := b4e205734 X0
               grind)
            | exact superpose b4e205734 b4e14
            | (have j1 := b4e205734 X0
               grind)
            | exact resolve b4e14 b4e205734
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e205734
          have b4e221368 : ∀ X0 : G, (k y (τ X0)) = (M.op y (τ X0)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e221333 X0
               have i₂ := b4e89 y X0
               grind)
            | exact superpose b4e89 b4e221333
            | (have j0 := b4e221333 X0
               grind)
            | exact resolve b4e221333 b4e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e89 b4e221333
          have b4e258686 : ∀ X0 : G, (σ (k y (k x x))) = X0 ∨ (k (k x x) (τ X0)) = (τ (M.op (σ (k x x)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e800 (k x x)
               have i₂ := b4e6671 (k x x) X0
               grind)
            | (have i₁ := b4e800 X0
               have i₂ := b4e6671 X0 (σ (k (k x x) X0))
               grind)
            | exact superpose b4e6671 b4e800
            | (have j1 := b4e6671 (k x x) X0
               grind)
            | exact resolve b4e800 b4e6671
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e800 b4e6671
          have b4e258741 : ∀ X0 : G, (σ (k y y)) = X0 ∨ (k (k x x) (τ X0)) = (τ (M.op (σ (k x x)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e258686 X0
               have i₂ := b4e799 y
               grind)
            | exact superpose b4e799 b4e258686
            | (have j0 := b4e258686 X0
               grind)
            | exact resolve b4e258686 b4e799
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e799 b4e258686
          have b4e258784 : ∀ X0 : G, (σ (M.op y y)) = X0 ∨ (k (k x x) (τ X0)) = (τ (M.op (σ (k x x)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e258741 X0
               have i₂ := b4e6710 y
               grind)
            | exact superpose b4e6710 b4e258741
            | (have j0 := b4e258741 X0
               grind)
            | exact resolve b4e258741 b4e6710
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e6710 b4e258741
          have b4e258803 : ∀ X0 : G, (σ x) = X0 ∨ (k (k x x) (τ X0)) = (τ (M.op (σ (k x x)) X0)) := by
            intro X0
            first
            | (have i₁ := b4e258784 X0
               have i₂ := b4e194375
               grind)
            | exact superpose b4e194375 b4e258784
            | (have j0 := b4e258784 X0
               grind)
            | exact resolve b4e258784 b4e194375
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e194375 b4e258784
          have b4e258815 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e258803 X0
               have i₂ := b4e760
               grind)
            | exact superpose b4e760 b4e258803
            | (have j0 := b4e258803 X0
               grind)
            | exact resolve b4e258803 b4e760
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e760 b4e258803
          have b4e258825 : ∀ X0 : G, (k y (τ X0)) = (τ (M.op (σ y) X0)) ∨ (σ x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e258815 X0
               have i₂ := b4e797 X0
               grind)
            | exact superpose b4e797 b4e258815
            | (have j0 := b4e258815 X0
               grind)
            | exact resolve b4e258815 b4e797
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e797 b4e258815
          have b4e258932 : (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e258825 (M.op (σ x) (σ y))
               have i₂ := b4e150
               grind)
            | exact superpose b4e150 b4e258825
            | (have j0 := b4e258825 (M.op (σ x) (σ y))
               grind)
            | exact resolve b4e258825 b4e150
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e150 b4e258825
          have b4e259053 : (τ (M.op (σ x) (σ y))) = (k y (τ (M.op (σ x) (σ y)))) := by
            first
            | (have r₁ := b4e258932
               have r₂ := b4e101
               grind)
            | exact resolve b4e258932 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e258932
          have b4e259243 : (τ (M.op (σ x) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e221368 (M.op (σ x) (σ y))
               have i₂ := b4e259053
               grind)
            | exact superpose b4e259053 b4e221368
            | (have j0 := b4e221368 (M.op (σ x) (σ y))
               grind)
            | exact resolve b4e221368 b4e259053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e221368 b4e259053
          have b4e259250 : (τ (M.op (σ x) (σ y))) = (M.op y (τ (M.op (σ x) (σ y)))) := by
            first
            | (have r₁ := b4e259243
               have r₂ := b4e101
               grind)
            | exact resolve b4e259243 b4e101
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e101 b4e259243
          have b4e260378 : ∀ X0 : G, (M.op (M.op y (τ (M.op (σ x) (σ y)))) X0) = (k (M.op y (τ (M.op (σ x) (σ y)))) X0) := by
            intro X0
            first
            | (have i₁ := b4e475 y (τ (M.op (σ x) (σ y))) x
               have i₂ := b4e259250
               grind)
            | exact superpose b4e259250 b4e475
            | exact resolve b4e475 b4e259250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e475
          have b4e260400 : ∀ X0 : G, (k (τ (M.op (σ x) (σ y))) X0) = (M.op (τ (M.op (σ x) (σ y))) X0) := by
            intro X0
            first
            | (have i₁ := b4e260378 X0
               have i₂ := b4e259250
               grind)
            | exact superpose b4e259250 b4e260378
            | exact resolve b4e260378 b4e259250
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e259250 b4e260378
          have b4e371562 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (τ (M.op (σ x) (σ y))) X0)) := by
            intro X0
            first
            | (have i₁ := b4e26 (M.op (σ x) (σ y)) X0
               have i₂ := b4e260400 X0
               grind)
            | exact superpose b4e260400 b4e26
            | exact resolve b4e26 b4e260400
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e260400
          have b4e371572 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (τ (M.op (σ x) (σ y))) X0)) := by
            intro X0
            first
            | (have i₁ := b4e371562 X0
               have i₂ := b4e1053 (σ X0)
               grind)
            | exact superpose b4e1053 b4e371562
            | exact resolve b4e371562 b4e1053
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1053 b4e371562
          have b4e423843 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op (τ (M.op (σ x) (σ y))) x))) := by
            first
            | (have i₁ := b4e371572 (M.op (τ (M.op (σ x) (σ y))) x)
               have i₂ := b4e127 (τ (M.op (σ x) (σ y)))
               grind)
            | exact superpose b4e127 b4e371572
            | exact resolve b4e371572 b4e127
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e127
          have b4e423851 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ x))) := by
            first
            | (have i₁ := b4e423843
               have i₂ := b4e371572 x
               grind)
            | exact superpose b4e371572 b4e423843
            | exact resolve b4e423843 b4e371572
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e371572 b4e423843
          have b4e423857 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ x)) (σ x)) := by
            first
            | (have i₁ := b4e423851
               have i₂ := b4e13 (M.op (σ x) (σ y)) (σ x)
               grind)
            | exact superpose b4e13 b4e423851
            | exact resolve b4e423851 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e423851
          have b4e423861 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b4e423857
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e423857
            | exact resolve b4e423857 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e423857
          have b4e423888 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e33
               have i₂ := b4e423861
               grind)
            | exact superpose b4e423861 b4e33
            | exact resolve b4e33 b4e423861
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33 b4e423861
          have b4e424205 : False := by grind
          exact b4e424205
        · have b5e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) X1) := by
            intro X0 X1
            grind
          have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : x ≠ (M.op y x) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b5e13 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e33 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X1 X1) (M.op X0 (M.op X0 X1))) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 (M.op X1 X1) X1
               have i₂ := b5e13 X0 X1
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e13 X0 x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : x ≠ (M.op x y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e32
               grind)
            | exact superpose b5e32 b5e21
            | exact resolve b5e21 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) ≠ X1 ∨ (M.op X1 (M.op X1 X1)) = (k X1 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X1 (M.op X1 X1)
               have i₂ := b5e13 X0 X1
               grind)
            | exact superpose b5e13 b5e16
            | (have j0 := b5e16 X1 (M.op X1 X1)
               grind)
            | (have r₁ := b5e16 (M.op (M.op X1 X1) X1) (M.op X1 X1)
               have r₂ := b5e13 (M.op X1 X1) X1
               grind)
            | exact resolve b5e16 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e41 : x = (k x y) ∨ x = (M.op y x) := by grind
          have b5e44 : x = (k x y) := by
            first
            | (have r₁ := b5e41
               have r₂ := b5e21
               grind)
            | exact resolve b5e41 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e47 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e18 X1 X2
               have i₂ := b5e18 X1 X0
               grind)
            | (have i₁ := b5e18 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X0)
               grind)
            | exact superpose b5e18 b5e18
            | (have j0 := b5e18 X1 X2
               have j1 := b5e18 X1 X2
               grind)
            | exact resolve b5e18 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b5e51 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e56 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e51
          have b5e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e56 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e56 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e56 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e56
          have b5e62 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1 X2
            first
            | (have j0 := b5e47 X0 X1 X2
               have j1 := b5e16 X1 X2
               grind)
            | (have r₁ := b5e47 (M.op X1 X0) X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e47 X0 X1 (M.op X1 X0)
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e47 X0 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e47 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e63 : ∀ X0 X1 X2 : G, X0 = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1 X2
            first
            | (have j0 := b5e62 X0 X1 X2
               have j1 := b5e16 X1 X2
               grind)
            | (have r₁ := b5e62 (M.op X1 X0) X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e62 X0 X1 (M.op X1 X0)
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e62 X1 X0 X2
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e62 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e155 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b5e61 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e61
          have b5e198 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e33 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e33 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e33
            | (have j1 := b5e18 X1 X0
               grind)
            | exact resolve b5e33 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e230 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e198 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e198 X1 X1
               have r₂ := b5e16 (M.op X1 X1) X1
               grind)
            | (have r₁ := b5e198 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e198 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e198
          have b5e245 : x ≠ y ∨ x = (k x x) := by
            first
            | (have i₁ := b5e155 x x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e155
            | (have j0 := b5e155 x x
               grind)
            | exact resolve b5e155 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e155
          have b5e395 : ∀ X0 : G, x = (M.op x y) ∨ y = X0 ∨ (M.op x X0) = (k x X0) := by
            intro X0
            first
            | (have i₁ := b5e44
               have i₂ := b5e63 y x X0
               grind)
            | exact superpose b5e63 b5e44
            | (have j1 := b5e63 y x X0
               grind)
            | exact resolve b5e44 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44 b5e63
          have b5e398 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ y = X0 := by
            intro X0
            first
            | (have j0 := b5e395 X0
               grind)
            | (have r₁ := b5e395 X0
               have r₂ := b5e36
               grind)
            | exact resolve b5e395 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e395
          have b5e416 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e38 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e38 X0 X1
               have i₂ := b5e18 X0 (M.op X0 X1)
               grind)
            | exact superpose b5e18 b5e38
            | (have j1 := b5e18 X1 X0
               grind)
            | (have r₁ := b5e38 X0 (M.op X0 X0)
               have r₂ := b5e18 X0 (M.op X0 (M.op X0 (M.op X0 X0)))
               grind)
            | exact resolve b5e38 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38
          have b5e432 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b5e416 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e416
          have b5e435 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e432 X0 X1
               have j1 := b5e16 X1 X0
               grind)
            | (have r₁ := b5e432 X1 X0
               have r₂ := b5e16 X0 X1
               grind)
            | exact resolve b5e432 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e432
          have b5e496 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e48 x x
               grind)
            | exact superpose b5e48 b5e24
            | (have j1 := b5e48 x x
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e48 x y
               grind)
            | exact resolve b5e24 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e559 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b5e496
          have b5e2089 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e559
               have i₂ := b5e398 x
               grind)
            | exact superpose b5e398 b5e559
            | (have j1 := b5e398 x
               grind)
            | exact resolve b5e559 b5e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e559
          have b5e2103 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e2089
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2089
            | exact resolve b5e2089 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2089
          have b5e2104 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
          clear b5e2103
          have b5e2112 : (σ x) ≠ (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2104
               grind)
            | exact superpose b5e2104 b5e24
            | exact resolve b5e24 b5e2104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e2140 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e435 (σ x) (σ x)
               have i₂ := b5e2104
               grind)
            | exact superpose b5e2104 b5e435
            | (have r₁ := b5e435 (σ x) (σ x)
               have r₂ := b5e2104
               grind)
            | exact resolve b5e435 b5e2104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e435 b5e2104
          have b5e2141 : (σ x) = (k (σ x) (σ x)) ∨ x = y := by grind
          clear b5e2140
          have b5e2145 : (σ x) = (σ (k x x)) ∨ x = y := by
            first
            | (have i₁ := b5e2141
               have i₂ := b5e19 x x
               grind)
            | exact superpose b5e19 b5e2141
            | exact resolve b5e2141 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2141
          have b5e2465 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = y := by
            first
            | (have i₁ := b5e2145
               have i₂ := b5e398 x
               grind)
            | exact superpose b5e398 b5e2145
            | (have j1 := b5e398 x
               grind)
            | exact resolve b5e2145 b5e398
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e398
          have b5e2472 : (k x x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b5e14 (k x x)
               have i₂ := b5e2145
               grind)
            | exact superpose b5e2145 b5e14
            | exact resolve b5e14 b5e2145
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2145
          have b5e2493 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
          clear b5e2465
          have b5e2506 : x = (k x x) ∨ x = y := by
            first
            | (have i₁ := b5e2472
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e2472
            | exact resolve b5e2472 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2472
          have b5e2511 : (σ x) = (σ y) ∨ x = y := by
            first
            | (have i₁ := b5e2493
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2493
            | exact resolve b5e2493 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2493
          have b5e2513 : x = (k x x) := by
            first
            | (have r₁ := b5e2506
               have r₂ := b5e245
               grind)
            | exact resolve b5e2506 b5e245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e245 b5e2506
          have b5e2518 : x = y := by
            first
            | (have r₁ := b5e2511
               have r₂ := b5e2112
               grind)
            | exact resolve b5e2511 b5e2112
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2112 b5e2511
          have b5e2591 : (M.op y x) = (M.op x x) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b5e34 x
               have i₂ := b5e230 x x
               grind)
            | exact superpose b5e230 b5e34
            | (have j1 := b5e230 x x
               grind)
            | exact resolve b5e34 b5e230
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34 b5e230
          have b5e2625 : y = (M.op y x) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b5e2591
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e2591
            | exact resolve b5e2591 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2591
          have b5e2646 : y = (M.op x y) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b5e2625
               have i₂ := b5e32
               grind)
            | exact superpose b5e32 b5e2625
            | exact resolve b5e2625 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32 b5e2625
          have b5e2661 : x = (M.op x x) ∨ (M.op x x) = (k x x) := by
            first
            | (have i₁ := b5e2646
               have i₂ := b5e2518
               grind)
            | exact superpose b5e2518 b5e2646
            | exact resolve b5e2646 b5e2518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2646
          have b5e2671 : (M.op x x) = (k x x) := by
            first
            | (have j1 := b5e16 x x
               grind)
            | (have r₁ := b5e2661
               have r₂ := b5e16 x x
               grind)
            | exact resolve b5e2661 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2661
          have b5e2681 : x = (M.op x x) := by
            first
            | (have i₁ := b5e2671
               have i₂ := b5e2513
               grind)
            | exact superpose b5e2513 b5e2671
            | exact resolve b5e2671 b5e2513
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2513 b5e2671
          have b5e2715 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b5e36
               have i₂ := b5e2518
               grind)
            | exact superpose b5e2518 b5e36
            | exact resolve b5e36 b5e2518
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e2518
          have b5e2744 : False := by grind
          exact b5e2744
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : x ≠ (M.op y x) := by grind
        have b6e21 : y ≠ (M.op x x) := by grind
        have b6e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e32 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
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
        have b6e35 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b6e32
        have b6e36 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e35
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e35
          | exact resolve b6e35 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e35
        have b6e47 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e36
             grind)
          | exact superpose b6e36 b6e19
          | exact resolve b6e19 b6e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e36
        have b6e67 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e47
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e47
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e47 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47
        have b6e68 : y = (M.op x x) ∨ x = (M.op y x) := by grind
        clear b6e67
        have b6e69 : x = (M.op y x) := by
          first
          | (have r₁ := b6e68
             have r₂ := b6e21
             grind)
          | exact resolve b6e68 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e70 : False := by grind
        exact b6e70
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ (M.op y x) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e44 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k x x)) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e44
            | exact resolve b7e44 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
          have b7e77 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e82 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b7e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e77
          have b7e87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 := by
            intro X0 X1
            first
            | (have j0 := b7e82 X0 X1
               have j1 := b7e16 X1 X0
               grind)
            | (have r₁ := b7e82 X1 X0
               have r₂ := b7e16 X0 X1
               grind)
            | exact resolve b7e82 b7e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e82
          have b7e609 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b7e74 x x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e74
            | exact resolve b7e74 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e74
          have b7e685 : (σ x) = (σ y) ∨ (σ y) = (σ (k x x)) := by grind
          clear b7e609
          have b7e715 : (σ y) = (σ (k x x)) := by
            first
            | (have r₁ := b7e685
               have r₂ := b7e47
               grind)
            | exact resolve b7e685 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e685
          have b7e752 : (k x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e715
               grind)
            | exact superpose b7e715 b7e14
            | exact resolve b7e14 b7e715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e715
          have b7e767 : y = (k x x) := by
            first
            | (have i₁ := b7e752
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e752
            | exact resolve b7e752 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e752
          have b7e814 : y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b7e87 x x
               have i₂ := b7e767
               grind)
            | exact superpose b7e767 b7e87
            | exact resolve b7e87 b7e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e815 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e18 x x
               have i₂ := b7e767
               grind)
            | exact superpose b7e767 b7e18
            | (have j0 := b7e18 x x
               grind)
            | exact resolve b7e18 b7e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e767
          have b7e816 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b7e815
          have b7e818 : x = (M.op x x) := by
            first
            | (have r₁ := b7e816
               have r₂ := b7e22
               grind)
            | exact resolve b7e816 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e816
          have b7e819 : x = y := by
            first
            | (have r₁ := b7e814
               have r₂ := b7e22
               grind)
            | exact resolve b7e814 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e814
          have b7e894 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e819
               grind)
            | exact superpose b7e819 b7e21
            | exact resolve b7e21 b7e819
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e819
          have b7e916 : False := by grind
          exact b7e916
        · have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ (M.op y x) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e79 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) ∨ (σ x) = (M.op X0 (σ x)) := by
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
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e81 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e79 X0
               have j1 := b8e16 (σ x) X0
               grind)
            | (have r₁ := b8e79 x
               have r₂ := b8e16 (σ x) x
               grind)
            | exact resolve b8e79 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e134 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e81 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e81
          have b8e135 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e134
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e134
            | exact resolve b8e134 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e134
          have b8e152 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e135
               grind)
            | exact superpose b8e135 b8e20
            | exact resolve b8e20 b8e135
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e191 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op y x) := by
            first
            | (have i₁ := b8e152
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e152
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e152 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e152
          have b8e192 : y = (M.op x x) ∨ x = (M.op y x) := by grind
          clear b8e191
          have b8e195 : x = (M.op y x) := by
            first
            | (have r₁ := b8e192
               have r₂ := b8e22
               grind)
            | exact resolve b8e192 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e192
          have b8e196 : False := by grind
          exact b8e196

/-- `Equation677`: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation677 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law677 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law677.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e40 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
      have b0e42 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
      have b0e44 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
      clear b0e42
      have b0e45 : (M.op x x) = (k x y) := by grind
      clear b0e40
      have b0e46 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e44
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e44
        | exact resolve b0e44 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e47 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
        first
        | (have i₁ := b0e46
           have i₂ := b0e45
           grind)
        | exact superpose b0e45 b0e46
        | exact resolve b0e46 b0e45
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45 b0e46
      have b0e48 : False := by grind
      exact b0e48
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e24 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e19
          | exact resolve b1e19 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e25 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e24
          | exact resolve b1e24 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24
        have b1e35 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b1e39 : (M.op x x) = (k x y) := by grind
        clear b1e35
        have b1e47 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e49 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e47
        have b1e50 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e49
             have r₂ := b1e23
             grind)
          | exact resolve b1e49 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e49
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
        have b1e52 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e51
             have i₂ := b1e39
             grind)
          | exact superpose b1e39 b1e51
          | exact resolve b1e51 b1e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39 b1e51
        have b1e53 : False := by grind
        exact b1e53
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b2e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e51 : (M.op x x) = (k x y) := by grind
        clear b2e48
        have b2e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e50 (σ X0)
             grind)
          | exact superpose b2e50 b2e18
          | exact resolve b2e18 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e60 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e53 X0
             have i₂ := b2e50 X0
             grind)
          | exact superpose b2e50 b2e53
          | exact resolve b2e53 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e53
        have b2e72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e72 X0 X1
             have i₂ := b2e60 X0
             grind)
          | exact superpose b2e60 b2e72
          | (have j0 := b2e72 X0 X1
             grind)
          | exact resolve b2e72 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e72
        have b2e518 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e86 x y
             grind)
          | exact superpose b2e86 b2e21
          | (have j1 := b2e86 x y
             grind)
          | exact resolve b2e21 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e569 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e518
             have r₂ := b2e23
             grind)
          | exact resolve b2e518 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e518
        have b2e578 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e569
             have r₂ := b2e22
             grind)
          | exact resolve b2e569 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e569
        have b2e584 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e578
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e578
          | exact resolve b2e578 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e578
        have b2e586 : False := by grind
        exact b2e586
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e23 : x ≠ (M.op x x) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
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
        have b3e47 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e49 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e47
        have b3e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e49
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e49
          | exact resolve b3e49 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e49
        have b3e61 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
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
        have b3e64 : x = (M.op x x) ∨ x = (k x y) := by grind
        clear b3e61
        have b3e65 : x = (k x y) := by
          first
          | (have r₁ := b3e64
             have r₂ := b3e23
             grind)
          | exact resolve b3e64 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e64
        have b3e88 : (σ x) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e25
             have i₂ := b3e50
             grind)
          | exact superpose b3e50 b3e25
          | exact resolve b3e25 b3e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e25 b3e50
        have b3e99 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e88
             have i₂ := b3e65
             grind)
          | exact superpose b3e65 b3e88
          | exact resolve b3e88 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e88
        have b3e100 : False := by grind
        exact b3e100
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
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e47 (σ X0)
               grind)
            | exact superpose b5e47 b5e19
            | exact resolve b5e19 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e49 X0
               have i₂ := b5e47 X0
               grind)
            | exact superpose b5e47 b5e49
            | exact resolve b5e49 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47 b5e49
          have b5e58 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by
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
          have b5e61 : x = (M.op x x) ∨ x = (k x y) := by grind
          clear b5e58
          have b5e62 : x = (k x y) := by
            first
            | (have r₁ := b5e61
               have r₂ := b5e25
               grind)
            | exact resolve b5e61 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e61
          have b5e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e67 X0 X1
               have i₂ := b5e54 X0
               grind)
            | exact superpose b5e54 b5e67
            | (have j0 := b5e67 X0 X1
               grind)
            | exact resolve b5e67 b5e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e470 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e81 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e81
          have b5e2285 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e470 x y
               have i₂ := b5e62
               grind)
            | exact superpose b5e62 b5e470
            | (have j0 := b5e470 x y
               grind)
            | exact resolve b5e470 b5e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62 b5e470
          have b5e2291 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e2285
          have b5e2295 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b5e2291
               have r₂ := b5e24
               grind)
            | exact resolve b5e2291 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2291
          have b5e2358 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e2295
               grind)
            | exact superpose b5e2295 b5e23
            | exact resolve b5e23 b5e2295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2295
          have b5e2384 : False := by grind
          exact b5e2384
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
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
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e51 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e51
          | exact resolve b6e51 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51
        have b6e68 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e23
          | exact resolve b6e23 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e52
        have b6e97 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
          first
          | (have i₁ := b6e68
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e68
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e68 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e68
        have b6e98 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
        clear b6e97
        have b6e99 : x = (M.op x y) := by
          first
          | (have r₁ := b6e98
             have r₂ := b6e20
             grind)
          | exact resolve b6e98 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e98
        have b6e100 : False := by grind
        exact b6e100
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e25 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e23
            | exact resolve b7e23 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b7e56 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e58 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e56
          have b7e59 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e58
               have r₂ := b7e25
               grind)
            | exact resolve b7e58 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e58
          have b7e60 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e59
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e59
            | exact resolve b7e59 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e59
          have b7e72 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e18 x y
               grind)
            | exact superpose b7e18 b7e60
            | (have j1 := b7e18 x y
               grind)
            | exact resolve b7e60 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e83 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e72
               have r₂ := b7e26
               grind)
            | exact resolve b7e72 b7e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e26 b7e72
          have b7e86 : x = (M.op x y) := by
            first
            | (have r₁ := b7e83
               have r₂ := b7e21
               grind)
            | exact resolve b7e83 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e87 : False := by grind
          exact b7e87
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b8e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 X0 X0
               have i₂ := b8e41 (σ X0)
               grind)
            | exact superpose b8e41 b8e19
            | exact resolve b8e19 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e48 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b8e43 X0
               have i₂ := b8e41 X0
               grind)
            | exact superpose b8e41 b8e43
            | exact resolve b8e43 b8e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e41 b8e43
          have b8e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e74 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e80 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e67 X0 X1
               have i₂ := b8e48 X0
               grind)
            | exact superpose b8e48 b8e67
            | (have j0 := b8e67 X0 X1
               grind)
            | exact resolve b8e67 b8e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e178 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e77 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e181 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e178 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e178 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e178 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e178 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e178
          have b8e448 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e80 x y
               grind)
            | exact superpose b8e80 b8e20
            | (have j1 := b8e80 x y
               grind)
            | exact resolve b8e20 b8e80
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80
          have b8e496 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e448
               have r₂ := b8e24
               grind)
            | exact resolve b8e448 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e448
          have b8e1003 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e496
               have i₂ := b8e181 x y
               grind)
            | exact superpose b8e181 b8e496
            | (have j1 := b8e181 x y
               grind)
            | exact resolve b8e496 b8e181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e181 b8e496
          have b8e1008 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (M.op x y) := by grind
          clear b8e1003
          have b8e1013 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e1008
               have r₂ := b8e22
               grind)
            | exact resolve b8e1008 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1008
          have b8e1018 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e1013
               grind)
            | exact superpose b8e1013 b8e23
            | exact resolve b8e23 b8e1013
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1013
          have b8e1032 : False := by grind
          exact b8e1032

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_pyx_pyx_pxx_pyx_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (M.op x y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
    · have b0e14 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
      have b0e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e57 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e52 X0
           have i₂ := b0e46 X0
           grind)
        | exact superpose b0e46 b0e52
        | exact resolve b0e52 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46 b0e52
      have b0e197 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e57 x
           grind)
        | exact superpose b0e57 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e57 x
           grind)
        | exact resolve b0e22 b0e57
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e57
      have b0e207 : False := by grind
      exact b0e207
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : (M.op x y) = (M.op x x) := by grind
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
        have b1e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e15 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e15 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e15
          | (have j0 := b1e15 X0 X0
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e15 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e15 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e15 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e101 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b1e16 X0 X1
             have i₂ := b1e17 X0 X1
             grind)
          | (have i₁ := b1e16 X0 X0
             have i₂ := b1e17 X0 X1
             grind)
          | exact superpose b1e17 b1e16
          | (have j0 := b1e16 X0 X1
             have j1 := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X1 X1
             have r₂ := b1e17 X1 X1
             grind)
          | (have r₁ := b1e16 X0 X1
             have r₂ := b1e17 X0 X1
             grind)
          | (have r₁ := b1e16 X0 X0
             have r₂ := b1e17 X0 X0
             grind)
          | exact resolve b1e16 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e101 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e101
        have b1e113 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e112 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e112
        have b1e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e91 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e116 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e115 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e115
        have b1e122 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e113 X0 X1
             have j1 := b1e15 X0 X1
             grind)
          | (have r₁ := b1e113 X0 X1
             have r₂ := b1e15 X0 X1
             grind)
          | (have r₁ := b1e113 X1 X1
             have r₂ := b1e15 X1 X1
             grind)
          | exact resolve b1e113 b1e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e113
        have b1e314 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e122 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e122
        have b1e321 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b1e314 X0 X1
             have j1 := b1e116 X0 X1
             grind)
          | (have r₁ := b1e314 X0 X1
             have r₂ := b1e116 X0 X1
             grind)
          | (have r₁ := b1e314 X0 X0
             have r₂ := b1e116 X0 X0
             grind)
          | exact resolve b1e314 b1e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e116 b1e314
        have b1e348 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X1 X0
             have i₂ := b1e321 (σ X1) (σ X0)
             grind)
          | exact superpose b1e321 b1e18
          | exact resolve b1e18 b1e321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e354 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b1e348 X0 X1
             have i₂ := b1e321 X1 X0
             grind)
          | exact superpose b1e321 b1e348
          | exact resolve b1e348 b1e321
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e321 b1e348
        have b1e1269 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e354 x y
             grind)
          | exact superpose b1e354 b1e23
          | exact resolve b1e23 b1e354
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e354
        have b1e1320 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e1269
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1269
          | exact resolve b1e1269 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1269
        have b1e1321 : False := by grind
        exact b1e1321
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
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
        have b2e83 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e15 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e15
          | (have j0 := b2e15 X0 X0
             have j1 := b2e17 X0 X1
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
        have b2e93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b2e16 X0 X1
             have i₂ := b2e17 X0 X1
             grind)
          | (have i₁ := b2e16 X0 X0
             have i₂ := b2e17 X0 X1
             grind)
          | exact superpose b2e17 b2e16
          | (have j0 := b2e16 X0 X1
             have j1 := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X1 X1
             have r₂ := b2e17 X1 X1
             grind)
          | (have r₁ := b2e16 X0 X1
             have r₂ := b2e17 X0 X1
             grind)
          | (have r₁ := b2e16 X0 X0
             have r₂ := b2e17 X0 X0
             grind)
          | exact resolve b2e16 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e104 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e93 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e105 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e104 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e104
        have b2e107 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e83 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e83
        have b2e108 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e107 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e107
        have b2e114 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e105 X0 X1
             have j1 := b2e15 X0 X1
             grind)
          | (have r₁ := b2e105 X0 X1
             have r₂ := b2e15 X0 X1
             grind)
          | (have r₁ := b2e105 X1 X1
             have r₂ := b2e15 X1 X1
             grind)
          | exact resolve b2e105 b2e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e105
        have b2e349 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e114 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e114
        have b2e356 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b2e349 X0 X1
             have j1 := b2e108 X0 X1
             grind)
          | (have r₁ := b2e349 X0 X1
             have r₂ := b2e108 X0 X1
             grind)
          | (have r₁ := b2e349 X0 X0
             have r₂ := b2e108 X0 X0
             grind)
          | exact resolve b2e349 b2e108
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e108 b2e349
        have b2e397 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X1 X0
             have i₂ := b2e356 (σ X1) (σ X0)
             grind)
          | exact superpose b2e356 b2e18
          | exact resolve b2e18 b2e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e404 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e397 X0 X1
             have i₂ := b2e356 X1 X0
             grind)
          | exact superpose b2e356 b2e397
          | exact resolve b2e397 b2e356
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e356 b2e397
        have b2e831 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e23
             have i₂ := b2e404 x y
             grind)
          | exact superpose b2e404 b2e23
          | exact resolve b2e23 b2e404
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e404
        have b2e869 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e831
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e831
          | exact resolve b2e831 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e831
        have b2e870 : False := by grind
        exact b2e870
  · rcases eq_or_ne (M.op x x) (M.op y x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x x) = (M.op y x) := by grind
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
        have b3e53 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
        have b3e54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e55 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
        clear b3e53
        have b3e56 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e55
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e55
          | exact resolve b3e55 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e55
        have b3e58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e54 (σ X0)
             grind)
          | exact superpose b3e54 b3e18
          | exact resolve b3e18 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e54 X0
             grind)
          | exact superpose b3e54 b3e58
          | exact resolve b3e58 b3e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54 b3e58
        have b3e71 : (M.op x x) ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b3e73 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by grind
        clear b3e71
        have b3e74 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e73
             have r₂ := b3e20
             grind)
          | exact resolve b3e73 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e73
        have b3e91 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e15 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e15
          | (have j0 := b3e15 X0 X0
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e15 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e15 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e15 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e16 X0 X1
             have i₂ := b3e17 X0 X1
             grind)
          | (have i₁ := b3e16 X0 X0
             have i₂ := b3e17 X0 X1
             grind)
          | exact superpose b3e17 b3e16
          | (have j0 := b3e16 X0 X1
             have j1 := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X1 X1
             have r₂ := b3e17 X1 X1
             grind)
          | (have r₁ := b3e16 X0 X1
             have r₂ := b3e17 X0 X1
             grind)
          | (have r₁ := b3e16 X0 X0
             have r₂ := b3e17 X0 X0
             grind)
          | exact resolve b3e16 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e113 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e17 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e102 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e102
        have b3e116 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e115 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e115
        have b3e118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e91 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e91
        have b3e119 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e118 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e118
        have b3e122 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e113 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e113 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e113 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e113 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e113
        have b3e126 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e116 X0 X1
             have j1 := b3e15 X0 X1
             grind)
          | (have r₁ := b3e116 X0 X1
             have r₂ := b3e15 X0 X1
             grind)
          | (have r₁ := b3e116 X1 X1
             have r₂ := b3e15 X1 X1
             grind)
          | exact resolve b3e116 b3e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116
        have b3e269 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e122 (σ y) (σ x)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e122
          | (have j0 := b3e122 (σ y) (σ x)
             grind)
          | exact resolve b3e122 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56 b3e122
        have b3e294 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e269
             have i₂ := b3e74
             grind)
          | exact superpose b3e74 b3e269
          | exact resolve b3e269 b3e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e74 b3e269
        have b3e298 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b3e294
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e294
          | exact resolve b3e294 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e294
        have b3e300 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
          first
          | (have r₁ := b3e298
             have r₂ := b3e65 x
             grind)
          | exact resolve b3e298 b3e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e65 b3e298
        have b3e301 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e300
             have i₂ := b3e18 y x
             grind)
          | exact superpose b3e18 b3e300
          | exact resolve b3e300 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e300
        have b3e357 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e126 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e126
        have b3e364 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b3e357 X0 X1
             have j1 := b3e119 X0 X1
             grind)
          | (have r₁ := b3e357 X0 X1
             have r₂ := b3e119 X0 X1
             grind)
          | (have r₁ := b3e357 X0 X0
             have r₂ := b3e119 X0 X0
             grind)
          | exact resolve b3e357 b3e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e119 b3e357
        have b3e705 : (M.op (σ x) (σ x)) = (σ (k y x)) := by
          first
          | (have i₁ := b3e22
             have i₂ := b3e301
             grind)
          | exact superpose b3e301 b3e22
          | exact resolve b3e22 b3e301
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e301
        have b3e726 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e705
             have i₂ := b3e364 y x
             grind)
          | exact superpose b3e364 b3e705
          | exact resolve b3e705 b3e364
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e364 b3e705
        have b3e731 : False := by grind
        exact b3e731
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b4e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
          have b4e119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 X0 X1
               have i₂ := b4e18 X0 X1
               grind)
            | (have i₁ := b4e17 X0 X0
               have i₂ := b4e18 X0 X1
               grind)
            | exact superpose b4e18 b4e17
            | (have j0 := b4e17 X0 X1
               have j1 := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X1 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e17 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e17 X0 X0
               have r₂ := b4e18 X0 X0
               grind)
            | exact resolve b4e17 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e133 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e119 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e119
          have b4e134 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e133 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e133
          have b4e136 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e109
          have b4e137 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e136 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e136
          have b4e145 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e134 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e134 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | (have r₁ := b4e134 X1 X1
               have r₂ := b4e16 X1 X1
               grind)
            | exact resolve b4e134 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e369 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e145 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e145
          have b4e376 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b4e369 X0 X1
               have j1 := b4e137 X0 X1
               grind)
            | (have r₁ := b4e369 X0 X1
               have r₂ := b4e137 X0 X1
               grind)
            | (have r₁ := b4e369 X0 X0
               have r₂ := b4e137 X0 X0
               grind)
            | exact resolve b4e369 b4e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137 b4e369
          have b4e418 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e19 X1 X0
               have i₂ := b4e376 (σ X1) (σ X0)
               grind)
            | exact superpose b4e376 b4e19
            | exact resolve b4e19 b4e376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e426 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e418 X0 X1
               have i₂ := b4e376 X1 X0
               grind)
            | exact superpose b4e376 b4e418
            | exact resolve b4e418 b4e376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e376 b4e418
          have b4e952 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e426 x y
               grind)
            | exact superpose b4e426 b4e20
            | (have r₁ := b4e20
               have r₂ := b4e426 x y
               grind)
            | exact resolve b4e20 b4e426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e426
          have b4e985 : False := by grind
          exact b4e985
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e16 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e16 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e16
            | (have j0 := b5e16 X0 X0
               have j1 := b5e18 X0 X1
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
          have b5e112 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b5e17 X0 X1
               have i₂ := b5e18 X0 X1
               grind)
            | (have i₁ := b5e17 X0 X0
               have i₂ := b5e18 X0 X1
               grind)
            | exact superpose b5e18 b5e17
            | (have j0 := b5e17 X0 X1
               have j1 := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X1 X1
               have r₂ := b5e18 X1 X1
               grind)
            | (have r₁ := b5e17 X0 X1
               have r₂ := b5e18 X0 X1
               grind)
            | (have r₁ := b5e17 X0 X0
               have r₂ := b5e18 X0 X0
               grind)
            | exact resolve b5e17 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e126 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e112 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
          have b5e127 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e126 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e126
          have b5e129 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e102 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e102
          have b5e130 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e129 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e129
          have b5e138 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e127 X0 X1
               have j1 := b5e16 X0 X1
               grind)
            | (have r₁ := b5e127 X0 X1
               have r₂ := b5e16 X0 X1
               grind)
            | (have r₁ := b5e127 X1 X1
               have r₂ := b5e16 X1 X1
               grind)
            | exact resolve b5e127 b5e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e127
          have b5e360 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e138 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e138
          have b5e367 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b5e360 X0 X1
               have j1 := b5e130 X0 X1
               grind)
            | (have r₁ := b5e360 X0 X1
               have r₂ := b5e130 X0 X1
               grind)
            | (have r₁ := b5e360 X0 X0
               have r₂ := b5e130 X0 X0
               grind)
            | exact resolve b5e360 b5e130
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130 b5e360
          have b5e409 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e19 X1 X0
               have i₂ := b5e367 (σ X1) (σ X0)
               grind)
            | exact superpose b5e367 b5e19
            | exact resolve b5e19 b5e367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e417 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e409 X0 X1
               have i₂ := b5e367 X1 X0
               grind)
            | exact superpose b5e367 b5e409
            | exact resolve b5e409 b5e367
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e367 b5e409
          have b5e889 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b5e20
               have i₂ := b5e417 x y
               grind)
            | exact superpose b5e417 b5e20
            | (have r₁ := b5e20
               have r₂ := b5e417 x y
               grind)
            | exact resolve b5e20 b5e417
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e417
          have b5e922 : False := by grind
          exact b5e922
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e18 (τ X0) X1
             have i₂ := b6e14 X0
             grind)
          | exact superpose b6e14 b6e18
          | exact resolve b6e18 b6e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b6e13 (k (τ X0) X1)
             have i₂ := b6e24 X0 X1
             grind)
          | exact superpose b6e24 b6e13
          | exact resolve b6e13 b6e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24
        have b6e88 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e15 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e15
          | (have j0 := b6e15 X0 X0
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e15 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e15 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e15 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e16 X0 X1
             have i₂ := b6e17 X0 X1
             grind)
          | (have i₁ := b6e16 X0 X0
             have i₂ := b6e17 X0 X1
             grind)
          | exact superpose b6e17 b6e16
          | (have j0 := b6e16 X0 X1
             have j1 := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X1 X1
             have r₂ := b6e17 X1 X1
             grind)
          | (have r₁ := b6e16 X0 X1
             have r₂ := b6e17 X0 X1
             grind)
          | (have r₁ := b6e16 X0 X0
             have r₂ := b6e17 X0 X0
             grind)
          | exact resolve b6e16 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e110 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e99 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e111 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e110 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e110
        have b6e113 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e88 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e88
        have b6e114 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e113 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e113
        have b6e120 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e111 X0 X1
             have j1 := b6e15 X0 X1
             grind)
          | (have r₁ := b6e111 X0 X1
             have r₂ := b6e15 X0 X1
             grind)
          | (have r₁ := b6e111 X1 X1
             have r₂ := b6e15 X1 X1
             grind)
          | exact resolve b6e111 b6e15
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e111
        have b6e329 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e120 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e120
        have b6e336 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
          intro X0 X1
          first
          | (have j0 := b6e329 X0 X1
             have j1 := b6e114 X0 X1
             grind)
          | (have r₁ := b6e329 X0 X1
             have r₂ := b6e114 X0 X1
             grind)
          | (have r₁ := b6e329 X0 X0
             have r₂ := b6e114 X0 X0
             grind)
          | exact resolve b6e329 b6e114
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114 b6e329
        have b6e368 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X1 X0
             have i₂ := b6e336 X1 (σ X0)
             grind)
          | exact superpose b6e336 b6e29
          | exact resolve b6e29 b6e336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e371 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b6e368 X0 X1
             have i₂ := b6e336 (τ X1) X0
             grind)
          | exact superpose b6e336 b6e368
          | exact resolve b6e368 b6e336
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e336 b6e368
        have b6e850 : (M.op x (τ (σ y))) = (τ (M.op (σ x) (σ x))) := by
          first
          | (have i₁ := b6e371 x (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e371
          | exact resolve b6e371 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e891 : (M.op x (τ (σ y))) = (M.op x (τ (σ x))) := by
          first
          | (have i₁ := b6e850
             have i₂ := b6e371 x (σ x)
             grind)
          | exact superpose b6e371 b6e850
          | exact resolve b6e850 b6e371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e371 b6e850
        have b6e905 : (M.op x x) = (M.op x (τ (σ y))) := by
          first
          | (have i₁ := b6e891
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e891
          | exact resolve b6e891 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e891
        have b6e911 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b6e905
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e905
          | exact resolve b6e905 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e905
        have b6e913 : False := by grind
        exact b6e913
      · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ y) (σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b7e22 : (M.op x x) ≠ (M.op y x) := by grind
          have b7e23 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
          have b7e75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e66 X0
               have i₂ := b7e64 X0
               grind)
            | exact superpose b7e64 b7e66
            | exact resolve b7e66 b7e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e64 b7e66
          have b7e83 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
          have b7e85 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e83
          have b7e86 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e85
               have r₂ := b7e23
               grind)
            | exact resolve b7e85 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e85
          have b7e87 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
          have b7e88 : (σ (k x y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e87
               have i₂ := b7e75 x
               grind)
            | exact superpose b7e75 b7e87
            | exact resolve b7e87 b7e75
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e75 b7e87
          have b7e93 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e88
               grind)
            | exact superpose b7e88 b7e14
            | exact resolve b7e14 b7e88
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e88
          have b7e94 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e93
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e93
            | exact resolve b7e93 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e93
          have b7e165 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e94
               grind)
            | exact superpose b7e94 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e166 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (M.op x x) := by grind
          clear b7e165
          have b7e168 : (M.op x y) = (M.op x x) := by
            first
            | (have r₁ := b7e166
               have r₂ := b7e22
               grind)
            | exact resolve b7e166 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e166
          have b7e170 : False := by grind
          exact b7e170
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e109 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
            | (have r₁ := b8e16 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e120 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e17 X0 X1
               have i₂ := b8e18 X0 X1
               grind)
            | (have i₁ := b8e17 X0 X0
               have i₂ := b8e18 X0 X1
               grind)
            | exact superpose b8e18 b8e17
            | (have j0 := b8e17 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | (have r₁ := b8e17 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e17 X0 X0
               have r₂ := b8e18 X0 X0
               grind)
            | exact resolve b8e17 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e120 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120
          have b8e133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e132 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e135 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e109 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e136 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e135 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135
          have b8e143 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e133 X0 X1
               have j1 := b8e16 X0 X1
               grind)
            | (have r₁ := b8e133 X0 X1
               have r₂ := b8e16 X0 X1
               grind)
            | (have r₁ := b8e133 X1 X1
               have r₂ := b8e16 X1 X1
               grind)
            | exact resolve b8e133 b8e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e133
          have b8e334 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e143 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e143
          have b8e341 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
            intro X0 X1
            first
            | (have j0 := b8e334 X0 X1
               have j1 := b8e136 X0 X1
               grind)
            | (have r₁ := b8e334 X0 X1
               have r₂ := b8e136 X0 X1
               grind)
            | (have r₁ := b8e334 X0 X0
               have r₂ := b8e136 X0 X0
               grind)
            | exact resolve b8e334 b8e136
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136 b8e334
          have b8e379 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e19 X1 X0
               have i₂ := b8e341 (σ X1) (σ X0)
               grind)
            | exact superpose b8e341 b8e19
            | exact resolve b8e19 b8e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e390 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e379 X0 X1
               have i₂ := b8e341 X1 X0
               grind)
            | exact superpose b8e341 b8e379
            | exact resolve b8e379 b8e341
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e341 b8e379
          have b8e922 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e390 x y
               grind)
            | exact superpose b8e390 b8e20
            | (have r₁ := b8e20
               have r₂ := b8e390 x y
               grind)
            | exact resolve b8e20 b8e390
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e390
          have b8e956 : False := by grind
          exact b8e956

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_x_pxx_pyx_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e23 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e28 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op X0 (σ x)))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e39 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b1e15 (σ x) (σ x)
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e15
          | exact resolve b1e15 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e41 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e42 : (σ x) = (k (σ x) (σ x)) := by grind
        clear b1e39
        have b1e44 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e42
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e42
          | exact resolve b1e42 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e42
        have b1e45 : (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e41 x
             grind)
          | exact superpose b1e41 b1e44
          | exact resolve b1e44 b1e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41 b1e44
        have b1e85 : (M.op x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (M.op x x)
             have i₂ := b1e45
             grind)
          | exact superpose b1e45 b1e13
          | exact resolve b1e13 b1e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e86 : x = (M.op x x) := by
          first
          | (have i₁ := b1e85
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e85
          | exact resolve b1e85 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e85
        have b1e102 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b1e12 x X0 x
             have i₂ := b1e86
             grind)
          | exact superpose b1e86 b1e12
          | exact resolve b1e12 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e103 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
          intro X0
          first
          | (have i₁ := b1e12 X0 x x
             have i₂ := b1e86
             grind)
          | exact superpose b1e86 b1e12
          | exact resolve b1e12 b1e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e86
        have b1e136 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b1e103 (M.op X0 x)
             have i₂ := b1e102 X0
             grind)
          | exact superpose b1e102 b1e103
          | exact resolve b1e103 b1e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e410 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b1e102 X0
             have i₂ := b1e136 X0
             grind)
          | exact superpose b1e136 b1e102
          | exact resolve b1e102 b1e136
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e102 b1e136
        have b1e511 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b1e103 X0
             have i₂ := b1e410 X0
             grind)
          | exact superpose b1e410 b1e103
          | exact resolve b1e103 b1e410
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e103 b1e410
        have b1e604 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 x) X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 X1 x
             have i₂ := b1e511 X0
             grind)
          | exact superpose b1e511 b1e12
          | exact resolve b1e12 b1e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e634 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b1e604 X0 X1
             have i₂ := b1e511 X1
             grind)
          | exact superpose b1e511 b1e604
          | exact resolve b1e604 b1e511
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e511 b1e604
        have b1e1666 : ∀ X0 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (M.op (σ x) (M.op X0 (σ x))) X0) := by
          intro X0
          first
          | (have i₁ := b1e634 (M.op (σ x) (M.op X0 (σ x))) X0
             have i₂ := b1e28 X0
             grind)
          | exact superpose b1e28 b1e634
          | exact resolve b1e634 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e1729 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b1e1666 x
             have i₂ := b1e634 (σ x) x
             grind)
          | exact superpose b1e634 b1e1666
          | exact resolve b1e1666 b1e634
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e634 b1e1666
        have b1e2000 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e1729 (σ y)
             grind)
          | exact superpose b1e1729 b1e23
          | (have r₁ := b1e23
             have r₂ := b1e1729 (σ y)
             grind)
          | exact resolve b1e23 b1e1729
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23 b1e1729
        have b1e2059 : False := by grind
        exact b1e2059
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : (M.op x y) = (M.op x x) := by grind
        have b2e21 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
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
        have b2e50 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k x y) := by
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
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e53 : (M.op x x) = (k x y) := by grind
        clear b2e50
        have b2e55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e18
          | exact resolve b2e18 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e62 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e55 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e55
          | exact resolve b2e55 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e55
        have b2e73 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
        have b2e93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e73 X0 X1
             have i₂ := b2e62 X0
             grind)
          | exact superpose b2e62 b2e73
          | (have j0 := b2e73 X0 X1
             grind)
          | exact resolve b2e73 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e73
        have b2e96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e93 X0 X1
             have i₂ := b2e62 X0
             grind)
          | exact superpose b2e62 b2e93
          | (have j0 := b2e93 X0 X1
             grind)
          | exact resolve b2e93 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e93
        have b2e126 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e62 x
             grind)
          | exact superpose b2e62 b2e22
          | exact resolve b2e22 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1207 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e96 x y
             grind)
          | exact superpose b2e96 b2e21
          | (have j1 := b2e96 x y
             grind)
          | exact resolve b2e21 b2e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e96
        have b2e1286 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) := by
          first
          | (have r₁ := b2e1207
             have r₂ := b2e23
             grind)
          | exact resolve b2e1207 b2e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e23 b2e1207
        have b2e1302 : (M.op (σ x) (σ x)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e1286
             have r₂ := b2e126
             grind)
          | exact resolve b2e1286 b2e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e126 b2e1286
        have b2e1315 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1302
             have i₂ := b2e53
             grind)
          | exact superpose b2e53 b2e1302
          | exact resolve b2e1302 b2e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e53 b2e1302
        have b2e1322 : False := by grind
        exact b2e1322
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e19
          | exact resolve b3e19 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e31 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
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
        have b3e33 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b3e12 x X0 x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b3e31 (M.op X0 x)
             have i₂ := b3e33 X0
             grind)
          | exact superpose b3e33 b3e31
          | exact resolve b3e31 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 : G, x ≠ (M.op x x) ∨ (M.op x x) = (k x (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have i₁ := b3e15 x (M.op (M.op X0 x) x)
             have i₂ := b3e33 X0
             grind)
          | exact superpose b3e33 b3e15
          | (have j0 := b3e15 x (M.op (M.op X0 x) x)
             grind)
          | exact resolve b3e15 b3e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b3e53 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b3e51
        have b3e55 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
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
        have b3e56 : ∀ X0 : G, (M.op x x) = (k x (M.op (M.op X0 x) x)) := by
          intro X0
          first
          | (have j0 := b3e48 X0
             grind)
          | (have r₁ := b3e48 X0
             have r₂ := b3e21
             grind)
          | exact resolve b3e48 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48
        have b3e58 : ∀ X0 : G, (M.op x x) = (k x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e56 X0
             have i₂ := b3e42 X0
             grind)
          | exact superpose b3e42 b3e56
          | exact resolve b3e56 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e59 : ∀ X0 : G, x = (k x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e58 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e58
          | exact resolve b3e58 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e58
        have b3e104 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
          intro X0
          first
          | (have i₁ := b3e33 X0
             have i₂ := b3e42 X0
             grind)
          | exact superpose b3e42 b3e33
          | exact resolve b3e33 b3e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e33 b3e42
        have b3e125 : ∀ X0 : G, (M.op X0 x) = X0 := by
          intro X0
          first
          | (have i₁ := b3e31 X0
             have i₂ := b3e104 X0
             grind)
          | exact superpose b3e104 b3e31
          | exact resolve b3e31 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e31
        have b3e146 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b3e104 X0
             have i₂ := b3e125 X0
             grind)
          | exact superpose b3e125 b3e104
          | exact resolve b3e104 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104
        have b3e148 : ∀ X0 : G, x = (k x X0) := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e125 X0
             grind)
          | exact superpose b3e125 b3e59
          | exact resolve b3e59 b3e125
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59 b3e125
        have b3e168 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b3e24
             have i₂ := b3e55
             grind)
          | exact superpose b3e55 b3e24
          | exact resolve b3e24 b3e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e24 b3e55
        have b3e183 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b3e168
             have i₂ := b3e148 y
             grind)
          | exact superpose b3e148 b3e168
          | exact resolve b3e168 b3e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e148 b3e168
        have b3e189 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b3e183
             have i₂ := b3e146 y
             grind)
          | exact superpose b3e146 b3e183
          | exact resolve b3e183 b3e146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146 b3e183
        have b3e190 : False := by grind
        exact b3e190
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b4e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b4e22 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : x ≠ (M.op x y) := by
            first
            | (have i₁ := b4e21
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e21
            | exact resolve b4e21 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e33 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
            intro X0
            first
            | (have i₁ := b4e13 X0 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
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
          have b4e67 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
            intro X0
            first
            | (have i₁ := b4e33 (M.op X0 x)
               have i₂ := b4e36 X0
               grind)
            | exact superpose b4e36 b4e33
            | exact resolve b4e33 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e67 X0
               grind)
            | exact superpose b4e67 b4e36
            | exact resolve b4e36 b4e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36 b4e67
          have b4e141 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b4e33 X0
               have i₂ := b4e121 X0
               grind)
            | exact superpose b4e121 b4e33
            | exact resolve b4e33 b4e121
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e160 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e121 X0
               have i₂ := b4e141 X0
               grind)
            | exact superpose b4e141 b4e121
            | exact resolve b4e121 b4e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121 b4e141
          have b4e188 : x ≠ x := by
            first
            | (have i₁ := b4e26
               have i₂ := b4e160 y
               grind)
            | exact superpose b4e160 b4e26
            | (have r₁ := b4e26
               have r₂ := b4e160 y
               grind)
            | exact resolve b4e26 b4e160
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e160
          have b4e201 : False := by grind
          exact b4e201
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X2) (M.op X0 X2))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e21 : (M.op x y) ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e25 : x ≠ (M.op x y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e21
            | exact resolve b5e21 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e28 : ∀ X0 : G, (M.op X0 (M.op x (M.op X0 x))) = X0 := by
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
          have b5e30 : ∀ X0 : G, x = (M.op x (M.op (M.op X0 x) x)) := by
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
          have b5e37 : ∀ X0 : G, (M.op X0 x) = (M.op (M.op X0 x) x) := by
            intro X0
            first
            | (have i₁ := b5e28 (M.op X0 x)
               have i₂ := b5e30 X0
               grind)
            | exact superpose b5e30 b5e28
            | exact resolve b5e28 b5e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e91 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b5e30 X0
               have i₂ := b5e37 X0
               grind)
            | exact superpose b5e37 b5e30
            | exact resolve b5e30 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e30 b5e37
          have b5e108 : ∀ X0 : G, (M.op X0 x) = X0 := by
            intro X0
            first
            | (have i₁ := b5e28 X0
               have i₂ := b5e91 X0
               grind)
            | exact superpose b5e91 b5e28
            | exact resolve b5e28 b5e91
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e28
          have b5e128 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b5e91 X0
               have i₂ := b5e108 X0
               grind)
            | exact superpose b5e108 b5e91
            | exact resolve b5e91 b5e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e91 b5e108
          have b5e160 : x ≠ x := by
            first
            | (have i₁ := b5e25
               have i₂ := b5e128 y
               grind)
            | exact superpose b5e128 b5e25
            | (have r₁ := b5e25
               have r₂ := b5e128 y
               grind)
            | exact resolve b5e25 b5e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e128
          have b5e172 : False := by grind
          exact b5e172
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x x) := by grind
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
        have b6e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
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
        have b6e53 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b6e51
        have b6e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e53
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e53
          | exact resolve b6e53 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e53
        have b6e69 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e54
             grind)
          | exact superpose b6e54 b6e23
          | exact resolve b6e23 b6e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23 b6e54
        have b6e113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b6e69
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e69
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e69 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e114 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
        clear b6e113
        have b6e115 : x = (M.op x x) := by
          first
          | (have r₁ := b6e114
             have r₂ := b6e20
             grind)
          | exact resolve b6e114 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e114
        have b6e116 : False := by grind
        exact b6e116
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e45 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) := by
            first
            | (have i₁ := b7e16 (σ x) (σ x)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e48 : (σ x) = (k (σ x) (σ x)) := by grind
          clear b7e45
          have b7e49 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e48
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e48
            | exact resolve b7e48 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e48
          have b7e50 : (σ x) = (σ (M.op x x)) := by
            first
            | (have i₁ := b7e49
               have i₂ := b7e47 x
               grind)
            | exact superpose b7e47 b7e49
            | exact resolve b7e49 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47 b7e49
          have b7e65 : (M.op x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e50
               grind)
            | exact superpose b7e50 b7e14
            | exact resolve b7e14 b7e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e66 : x = (M.op x x) := by
            first
            | (have i₁ := b7e65
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e65
            | exact resolve b7e65 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65
          have b7e69 : False := by grind
          exact b7e69
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e78 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
            | exact resolve b8e16 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e78 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e78
          have b8e248 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e83 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e251 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b8e248 X0 X1
               have j1 := b8e18 X0 X1
               grind)
            | (have r₁ := b8e248 X0 X1
               have r₂ := b8e18 X0 X1
               grind)
            | (have r₁ := b8e248 X1 X1
               have r₂ := b8e18 X1 X1
               grind)
            | exact resolve b8e248 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e248
          have b8e1423 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e251 (σ x) X0
               grind)
            | exact superpose b8e251 b8e24
            | (have j1 := b8e251 (σ x) X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e251 (σ x) x
               grind)
            | exact resolve b8e24 b8e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e1431 : ∀ X0 : G, (M.op (σ x) X0) = (k (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e1423 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1423
          have b8e1552 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (k x X0)) := by
            intro X0
            first
            | (have i₁ := b8e19 x X0
               have i₂ := b8e1431 (σ X0)
               grind)
            | exact superpose b8e1431 b8e19
            | exact resolve b8e19 b8e1431
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1431
          have b8e1633 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1552 y
               grind)
            | exact superpose b8e1552 b8e20
            | exact resolve b8e20 b8e1552
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1552
          have b8e1746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e1633
               have i₂ := b8e251 x y
               grind)
            | exact superpose b8e251 b8e1633
            | (have j1 := b8e251 x x
               grind)
            | exact resolve b8e1633 b8e251
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e251 b8e1633
          have b8e1755 : x = (M.op x x) := by grind
          clear b8e1746
          have b8e1758 : False := by grind
          exact b8e1758

/-- `Equation854`: `x = x ◇ ((y ◇ z) ◇ (x ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pxy_x_pxy_Equation854 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law854 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law854.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
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
      have b0e44 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (M.op X0 y) = (k X0 y) := by
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
      have b0e45 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
      have b0e269 : (M.op x y) = (k x y) := by
        first
        | (have j0 := b0e44 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e453 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
        first
        | (have j0 := b0e45 (σ x)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e455 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
        first
        | (have i₁ := b0e453
           have i₂ := b0e17 x y
           grind)
        | exact superpose b0e17 b0e453
        | exact resolve b0e453 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e453
      have b0e461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e455
           have i₂ := b0e269
           grind)
        | exact superpose b0e269 b0e455
        | exact resolve b0e455 b0e269
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e269 b0e455
      have b0e464 : False := by grind
      exact b0e464
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
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : (M.op x x) = (M.op y y) := by grind
        have b2e21 : (M.op (σ x) (σ x)) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b2e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b2e18 X0 X0
             have i₂ := b2e52 (σ X0)
             grind)
          | exact superpose b2e52 b2e18
          | exact resolve b2e18 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e54 X0
             have i₂ := b2e52 X0
             grind)
          | exact superpose b2e52 b2e54
          | exact resolve b2e54 b2e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e52 b2e54
        have b2e141 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e61 y
             grind)
          | exact superpose b2e61 b2e21
          | exact resolve b2e21 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e150 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e141
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e141
          | exact resolve b2e141 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e141
        have b2e153 : False := by grind
        exact b2e153
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
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : (M.op x x) ≠ (M.op y y) := by grind
        have b6e22 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e54 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b6e18 X0 X0
             have i₂ := b6e52 (σ X0)
             grind)
          | exact superpose b6e52 b6e18
          | exact resolve b6e18 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e54 X0
             have i₂ := b6e52 X0
             grind)
          | exact superpose b6e52 b6e54
          | exact resolve b6e54 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52 b6e54
        have b6e135 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e61 y
             grind)
          | exact superpose b6e61 b6e22
          | exact resolve b6e22 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e144 : (σ (M.op y y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e135
             have i₂ := b6e61 x
             grind)
          | exact superpose b6e61 b6e135
          | exact resolve b6e135 b6e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e135
        have b6e161 : (M.op y y) = (τ (σ (M.op x x))) := by
          first
          | (have i₁ := b6e13 (M.op y y)
             have i₂ := b6e144
             grind)
          | exact superpose b6e144 b6e13
          | exact resolve b6e13 b6e144
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e144
        have b6e162 : (M.op x x) = (M.op y y) := by
          first
          | (have i₁ := b6e161
             have i₂ := b6e13 (M.op x x)
             grind)
          | exact superpose b6e13 b6e161
          | exact resolve b6e161 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e161
        have b6e168 : False := by grind
        exact b6e168
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
        · have b8e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
          clear b8e42 b8e44
          have b8e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e74 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k X0 y) = (M.op X0 y) ∨ y = X0 := by
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
               have r₂ := b8e18 x y
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 y x
               grind)
            | (have r₁ := b8e21
               have r₂ := b8e18 (M.op x x) (M.op y y)
               grind)
            | exact resolve b8e21 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e77 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e49 X1
               grind)
            | exact superpose b8e49 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e77 X0 X1
               have i₂ := b8e49 X0
               grind)
            | exact superpose b8e49 b8e77
            | (have j0 := b8e77 X0 X1
               grind)
            | exact resolve b8e77 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e77
          have b8e169 : (M.op x y) = (k x y) ∨ x = y := by
            first
            | (have j0 := b8e74 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e74
          have b8e170 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b8e169
               have r₂ := b8e22
               grind)
            | exact resolve b8e169 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e169
          have b8e228 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e23
               have i₂ := b8e49 y
               grind)
            | exact superpose b8e49 b8e23
            | exact resolve b8e23 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e243 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e228
               have i₂ := b8e49 x
               grind)
            | exact superpose b8e49 b8e228
            | exact resolve b8e228 b8e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e49 b8e228
          have b8e963 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e83 x y
               grind)
            | exact superpose b8e83 b8e20
            | (have j1 := b8e83 x y
               grind)
            | exact resolve b8e20 b8e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e83
          have b8e1007 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e963
               have r₂ := b8e243
               grind)
            | exact resolve b8e963 b8e243
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e243 b8e963
          have b8e1016 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1007
               have r₂ := b8e24
               grind)
            | exact resolve b8e1007 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1007
          have b8e1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e1016
               have i₂ := b8e170
               grind)
            | exact superpose b8e170 b8e1016
            | exact resolve b8e1016 b8e170
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e170 b8e1016
          have b8e1020 : False := by grind
          exact b8e1020
