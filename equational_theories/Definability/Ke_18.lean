import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4441`: `x ◇ (y ◇ x) = (x ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_x_y_pxy_Equation4441 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4441 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4441.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : y ≠ y ∨ x = (k x y) := by
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
        have b1e27 : x = (k x y) := by grind
        clear b1e24
        have b1e52 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e55 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e52
        have b1e57 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e55
             have r₂ := b1e21
             grind)
          | exact resolve b1e55 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55
        have b1e58 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e57
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e57
          | exact resolve b1e57 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57
        have b1e59 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e58
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e58
          | exact resolve b1e58 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27 b1e58
        have b1e60 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e22
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e22
          | exact resolve b1e22 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e61 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e59
             grind)
          | exact superpose b1e59 b1e21
          | exact resolve b1e21 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59
        have b1e68 : False := by grind
        exact b1e68
      · have b2e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e36 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 x X0 y X1
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X0 X2 : G, (M.op y X0) = (M.op y X2) := by
          intro X0 X2
          first
          | (have i₁ := b2e36 x X2
             have i₂ := b2e36 x X0
             grind)
          | exact superpose b2e36 b2e36
          | exact resolve b2e36 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e58 : y ≠ y ∨ x = (M.op y x) ∨ x = (k y x) := by
          first
          | (have i₁ := b2e16 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e16
          | (have j0 := b2e16 y x
             grind)
          | (have r₁ := b2e16 y x
             have r₂ := b2e20
             grind)
          | exact resolve b2e16 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e61 : x = (k y x) ∨ x = (M.op y x) := by grind
        clear b2e58
        have b2e82 : ∀ X0 X2 X3 : G, (M.op y X0) = (M.op (M.op y X2) X3) := by
          intro X0 X2 X3
          first
          | (have i₁ := b2e12 y x X2 X3
             have i₂ := b2e44 (M.op x y) X0
             grind)
          | (have i₁ := b2e12 y x X2 X3
             have i₂ := b2e44 X0 (M.op x y)
             grind)
          | exact superpose b2e44 b2e12
          | exact resolve b2e12 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e1514 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e86 y x
             grind)
          | exact superpose b2e86 b2e21
          | (have j1 := b2e86 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e86 y x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e86 x y
             grind)
          | exact resolve b2e21 b2e86
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e86
        have b2e1546 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
        clear b2e1514
        have b2e1553 : (M.op (σ y) (σ x)) = (σ (k y x)) := by
          first
          | (have r₁ := b2e1546
             have r₂ := b2e22
             grind)
          | exact resolve b2e1546 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1546
        have b2e1651 : (σ x) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e1553
             grind)
          | exact superpose b2e1553 b2e22
          | exact resolve b2e22 b2e1553
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1553
        have b2e1676 : (σ x) ≠ (σ x) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b2e1651
             have i₂ := b2e61
             grind)
          | exact superpose b2e61 b2e1651
          | exact resolve b2e1651 b2e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e61
        have b2e1678 : x = (M.op y x) := by grind
        clear b2e1676
        have b2e1834 : ∀ X0 : G, x = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e44 X0 x
             have i₂ := b2e1678
             grind)
          | exact superpose b2e1678 b2e44
          | exact resolve b2e44 b2e1678
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44
        have b2e1835 : ∀ X0 X1 : G, (M.op y X0) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e82 X0 x X1
             have i₂ := b2e1678
             grind)
          | exact superpose b2e1678 b2e82
          | exact resolve b2e82 b2e1678
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e82
        have b2e1847 : x ≠ x ∨ y = (k y x) := by
          first
          | (have i₁ := b2e15 y x
             have i₂ := b2e1678
             grind)
          | exact superpose b2e1678 b2e15
          | (have j0 := b2e15 y x
             grind)
          | (have r₁ := b2e15 y x
             have r₂ := b2e1678
             grind)
          | exact resolve b2e15 b2e1678
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1678
        have b2e1869 : y = (k y x) := by grind
        clear b2e1847
        have b2e2402 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e1651
             have i₂ := b2e1869
             grind)
          | exact superpose b2e1869 b2e1651
          | exact resolve b2e1651 b2e1869
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1651 b2e1869
        have b2e3535 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b2e1834 x
             have i₂ := b2e1835 x X0
             grind)
          | exact superpose b2e1835 b2e1834
          | exact resolve b2e1834 b2e1835
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1834 b2e1835
        have b2e4254 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e3535 y
             grind)
          | exact superpose b2e3535 b2e20
          | exact resolve b2e20 b2e3535
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3535
        have b2e4973 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e2402
             have i₂ := b2e4254
             grind)
          | exact superpose b2e4254 b2e2402
          | exact resolve b2e2402 b2e4254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2402 b2e4254
        have b2e4975 : False := by grind
        exact b2e4975
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x y) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e25 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b3e26 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b3e25
        have b3e28 : (σ x) = (σ (k x y)) := by
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
        have b3e46 : (k x y) = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e28
             grind)
          | exact superpose b3e28 b3e13
          | exact resolve b3e13 b3e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e47 : x = (k x y) := by
          first
          | (have i₁ := b3e46
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e46
          | exact resolve b3e46 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e46
        have b3e53 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) := by
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
        have b3e54 : y = (M.op x y) ∨ y = (k x y) := by grind
        clear b3e53
        have b3e56 : y = (k x y) := by
          first
          | (have r₁ := b3e54
             have r₂ := b3e20
             grind)
          | exact resolve b3e54 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e71 : x = y := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e47
             grind)
          | exact superpose b3e47 b3e56
          | exact resolve b3e56 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47 b3e56
        have b3e102 : y ≠ (M.op y y) := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e71
             grind)
          | exact superpose b3e71 b3e20
          | exact resolve b3e20 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e103 : y = (M.op y y) := by
          first
          | (have i₁ := b3e21
             have i₂ := b3e71
             grind)
          | exact superpose b3e71 b3e21
          | exact resolve b3e21 b3e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e71
        have b3e111 : False := by grind
        exact b3e111
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
            intro X0 X1 X2 X3
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op x y) := by grind
          have b4e22 : x = (M.op y x) := by grind
          have b4e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e37 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b4e13 X2 (M.op X0 x) X4 X5
               have i₂ := b4e13 X0 X1 x X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X4) X5) := by
            intro X0 X1 X2 X4 X5
            first
            | (have i₁ := b4e13 X0 x X4 X5
               have i₂ := b4e13 X0 x X1 X2
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 (σ x) X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 X1 : G, (M.op y (M.op X0 y)) = (M.op x X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 y X0 x X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X0) ∨ (k X0 (M.op X3 X0)) = X0 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e16 X0 (M.op X3 X0)
               have i₂ := b4e13 X0 X3 X1 X2
               grind)
            | exact superpose b4e13 b4e16
            | (have j0 := b4e16 X0 (M.op X3 X0)
               grind)
            | (have r₁ := b4e16 X3 (M.op (M.op X3 X2) X3)
               have r₂ := b4e13 X3 (M.op X3 X2) X2 X3
               grind)
            | (have r₁ := b4e16 (M.op X0 X2) (M.op X0 (M.op X1 X0))
               have r₂ := b4e13 X0 X1 X2 (M.op X0 (M.op X1 X0))
               grind)
            | exact resolve b4e16 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e50 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e44 x X2
               have i₂ := b4e44 x X0
               grind)
            | exact superpose b4e44 b4e44
            | exact resolve b4e44 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op y X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 y x X2 X3
               have i₂ := b4e44 x X0
               grind)
            | exact superpose b4e44 b4e13
            | exact resolve b4e13 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e98 : ∀ X0 : G, y ≠ (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e21
               have i₂ := b4e50 y X0
               grind)
            | (have i₁ := b4e21
               have i₂ := b4e50 X0 y
               grind)
            | exact superpose b4e50 b4e21
            | exact resolve b4e21 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e104 : ∀ X0 X2 X3 : G, (M.op x X0) = (M.op (M.op x X2) X3) := by
            intro X0 X2 X3
            first
            | (have i₁ := b4e13 x x X2 X3
               have i₂ := b4e50 (M.op x x) X0
               grind)
            | (have i₁ := b4e13 x x X2 X3
               have i₂ := b4e50 X0 (M.op x x)
               grind)
            | exact superpose b4e50 b4e13
            | exact resolve b4e13 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e105 : ∀ X0 X1 : G, (M.op x X1) = (M.op y (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e44 x X1
               have i₂ := b4e50 y X0
               grind)
            | (have i₁ := b4e44 x X1
               have i₂ := b4e50 X0 y
               grind)
            | exact superpose b4e50 b4e44
            | exact resolve b4e44 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44
          have b4e118 : ∀ X0 X1 : G, y ≠ (M.op (M.op x X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e98 (M.op x x)
               have i₂ := b4e13 x x X0 X1
               grind)
            | exact superpose b4e13 b4e98
            | exact resolve b4e98 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e98
          have b4e137 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) X0) X1) = (M.op (σ x) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e39 (σ y) X0 X1 (σ x) X2
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e39
            | exact resolve b4e39 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39
          have b4e295 : ∀ X0 X1 X3 : G, (M.op (σ x) X3) = (M.op (σ y) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e43 (M.op X0 x) X3
               have i₂ := b4e13 X0 X1 x (σ y)
               grind)
            | exact superpose b4e13 b4e43
            | exact resolve b4e43 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e299 : ∀ X0 X2 : G, (M.op (σ x) X0) = (M.op (σ x) X2) := by
            intro X0 X2
            first
            | (have i₁ := b4e43 x X2
               have i₂ := b4e43 x X0
               grind)
            | exact superpose b4e43 b4e43
            | exact resolve b4e43 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e743 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e20
               have i₂ := b4e299 (σ y) X0
               grind)
            | (have i₁ := b4e20
               have i₂ := b4e299 X0 (σ y)
               grind)
            | exact superpose b4e299 b4e20
            | exact resolve b4e20 b4e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e744 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e23
               have i₂ := b4e299 (σ y) X0
               grind)
            | (have i₁ := b4e23
               have i₂ := b4e299 X0 (σ y)
               grind)
            | exact superpose b4e299 b4e23
            | exact resolve b4e23 b4e299
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e299
          have b4e819 : ∀ X0 X1 : G, (k X0 (M.op (M.op X0 X1) X0)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e47 X0 X1 x (M.op X0 X1)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47
          have b4e1116 : ∀ X0 : G, y = (k y (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e819 y x
               have i₂ := b4e54 X0 x y
               grind)
            | exact superpose b4e54 b4e819
            | exact resolve b4e819 b4e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54
          have b4e1120 : ∀ X0 X1 : G, (k X0 (M.op X0 (M.op X1 X0))) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e819 X0 x
               have i₂ := b4e13 X0 X1 x X0
               grind)
            | exact superpose b4e13 b4e819
            | exact resolve b4e819 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e819
          have b4e1816 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e16 (σ X1) (σ X0)
               have i₂ := b4e76 X0 X1
               grind)
            | exact superpose b4e76 b4e16
            | (have j0 := b4e16 (σ X1) (σ X0)
               have j1 := b4e76 X0 X1
               grind)
            | (have r₁ := b4e16 (σ X1) (σ X0)
               have r₂ := b4e76 X0 X1
               grind)
            | (have r₁ := b4e16 (σ X0) (σ X1)
               have r₂ := b4e76 X0 X1
               grind)
            | exact resolve b4e16 b4e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1837 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e76 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e76
          have b4e1839 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b4e1837 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1837
          have b4e1842 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e1816 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1816
          have b4e1851 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1842 X0 X1
               have i₂ := b4e19 X1 X0
               grind)
            | exact superpose b4e19 b4e1842
            | (have j0 := b4e1842 X0 X1
               grind)
            | exact resolve b4e1842 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1842
          have b4e1948 : ∀ X0 X1 : G, (M.op x X0) ≠ (M.op x X1) ∨ y = (M.op (M.op x X1) y) ∨ y = (k (M.op x X1) y) := by
            intro X0 X1
            first
            | (have i₁ := b4e17 (M.op x X1) y
               have i₂ := b4e105 X1 X0
               grind)
            | exact superpose b4e105 b4e17
            | (have j0 := b4e17 (M.op x X1) y
               grind)
            | (have r₁ := b4e17 (M.op y (M.op x X0)) x
               have r₂ := b4e105 X0 (M.op y (M.op x X0))
               grind)
            | (have r₁ := b4e17 (M.op x X1) y
               have r₂ := b4e105 X1 X1
               grind)
            | exact resolve b4e17 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e105
          have b4e1966 : ∀ X1 : G, y = (M.op (M.op x X1) y) ∨ y = (k (M.op x X1) y) := by
            intro X1
            first
            | (have j0 := b4e1948 x X1
               grind)
            | (have r₁ := b4e1948 x x
               have r₂ := b4e50 x x
               grind)
            | (have r₁ := b4e1948 x x
               have r₂ := b4e50 x x
               grind)
            | exact resolve b4e1948 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1948
          have b4e1969 : ∀ X1 : G, y = (k (M.op x X1) y) := by
            intro X1
            first
            | (have j0 := b4e1966 X1
               grind)
            | (have r₁ := b4e1966 x
               have r₂ := b4e118 x y
               grind)
            | exact resolve b4e1966 b4e118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e118 b4e1966
          have b4e2011 : ∀ X0 X1 : G, (M.op (σ x) X1) ≠ (σ (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e743 X1
               have i₂ := b4e50 y X0
               grind)
            | (have i₁ := b4e743 X1
               have i₂ := b4e50 X0 y
               grind)
            | exact superpose b4e50 b4e743
            | exact resolve b4e743 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50 b4e743
          have b4e2549 : ∀ X0 X1 : G, (σ y) ≠ (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e744 x
               have i₂ := b4e137 X0 X1 x
               grind)
            | exact superpose b4e137 b4e744
            | exact resolve b4e744 b4e137
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e137 b4e744
          have b4e2688 : ∀ X0 X1 : G, (M.op x X1) = (k (M.op x X1) (M.op x X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e1120 (M.op x X1) x
               have i₂ := b4e104 X0 X1 (M.op x (M.op x X1))
               grind)
            | exact superpose b4e104 b4e1120
            | exact resolve b4e1120 b4e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e104 b4e1120
          have b4e3418 : ∀ X0 X1 : G, (σ y) ≠ (M.op (σ y) (M.op X0 (M.op X1 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e2549 x x
               have i₂ := b4e37 X0 X1 (σ y) x x
               grind)
            | exact superpose b4e37 b4e2549
            | exact resolve b4e2549 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e2549
          have b4e8791 : ∀ X0 X1 X3 : G, (M.op (σ y) (M.op X0 (M.op X1 X0))) ≠ (σ (M.op x X3)) := by
            intro X0 X1 X3
            first
            | (have i₁ := b4e2011 X3 x
               have i₂ := b4e295 X0 X1 x
               grind)
            | exact superpose b4e295 b4e2011
            | exact resolve b4e2011 b4e295
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e295 b4e2011
          have b4e47573 : ∀ X0 : G, (σ (M.op x X0)) ≠ (σ (M.op x X0)) ∨ (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b4e1839 (M.op x X0)
               have i₂ := b4e2688 X0 X0
               grind)
            | exact superpose b4e2688 b4e1839
            | (have j0 := b4e1839 (M.op x X0)
               grind)
            | exact resolve b4e1839 b4e2688
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1839 b4e2688
          have b4e47575 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
            intro X0
            first
            | (have j0 := b4e47573 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47573
          have b4e289527 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (M.op (σ (M.op x X0)) (σ (M.op x X0)))) := by
            intro X0
            first
            | (have i₁ := b4e3418 (σ (M.op x X0)) (σ (M.op x X0))
               have i₂ := b4e47575 X0
               grind)
            | exact superpose b4e47575 b4e3418
            | exact resolve b4e3418 b4e47575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3418
          have b4e289542 : ∀ X0 X1 : G, (σ (M.op x X1)) ≠ (M.op (σ y) (M.op (σ (M.op x X0)) (σ (M.op x X0)))) := by
            intro X0 X1
            first
            | (have i₁ := b4e8791 (σ (M.op x X0)) (σ (M.op x X0)) X1
               have i₂ := b4e47575 X0
               grind)
            | exact superpose b4e47575 b4e8791
            | exact resolve b4e8791 b4e47575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e8791
          have b4e289571 : ∀ X0 X1 : G, (σ (M.op x X1)) ≠ (M.op (σ y) (σ (M.op x X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e289542 X0 X1
               have i₂ := b4e47575 X0
               grind)
            | exact superpose b4e47575 b4e289542
            | exact resolve b4e289542 b4e47575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e289542
          have b4e289581 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b4e289527 X0
               have i₂ := b4e47575 X0
               grind)
            | exact superpose b4e47575 b4e289527
            | exact resolve b4e289527 b4e47575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e289527
          have b4e291575 : ∀ X0 : G, (σ y) ≠ (σ (k y (M.op x X0))) ∨ (σ (M.op x X0)) = (σ (k (M.op x X0) y)) ∨ (σ (M.op x X0)) = (M.op (σ y) (σ (M.op x X0))) := by
            intro X0
            first
            | (have i₁ := b4e289581 X0
               have i₂ := b4e1851 y (M.op x X0)
               grind)
            | exact superpose b4e1851 b4e289581
            | (have j1 := b4e1851 y (M.op x X0)
               grind)
            | exact resolve b4e289581 b4e1851
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1851
          have b4e291580 : ∀ X0 : G, (σ y) ≠ (σ (k y (M.op x X0))) ∨ (σ (M.op x X0)) = (σ (k (M.op x X0) y)) := by
            intro X0
            first
            | (have j0 := b4e291575 X0
               grind)
            | (have r₁ := b4e291575 X0
               have r₂ := b4e289571 X0 X0
               grind)
            | exact resolve b4e291575 b4e289571
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e289571 b4e291575
          have b4e291606 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ (M.op x X0)) = (σ (k (M.op x X0) y)) := by
            intro X0
            first
            | (have i₁ := b4e291580 X0
               have i₂ := b4e1116 X0
               grind)
            | exact superpose b4e1116 b4e291580
            | (have j0 := b4e291580 X0
               grind)
            | exact resolve b4e291580 b4e1116
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1116 b4e291580
          have b4e291607 : ∀ X0 : G, (σ (M.op x X0)) = (σ (k (M.op x X0) y)) := by
            intro X0
            first
            | (have j0 := b4e291606 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e291606
          have b4e291623 : ∀ X0 : G, (σ y) = (σ (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b4e291607 X0
               have i₂ := b4e1969 X0
               grind)
            | exact superpose b4e1969 b4e291607
            | exact resolve b4e291607 b4e1969
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1969 b4e291607
          have b4e292607 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e47575 x
               have i₂ := b4e291623 x
               grind)
            | exact superpose b4e291623 b4e47575
            | exact resolve b4e47575 b4e291623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47575
          have b4e292612 : (σ y) ≠ (M.op (σ y) (σ y)) := by
            first
            | (have i₁ := b4e289581 x
               have i₂ := b4e291623 x
               grind)
            | exact superpose b4e291623 b4e289581
            | exact resolve b4e289581 b4e291623
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e289581 b4e291623
          have b4e292736 : False := by grind
          exact b4e292736
        · have b5e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x y) := by grind
          have b5e22 : x = (M.op y x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e60 : x ≠ x ∨ y = (M.op x y) ∨ y = (k x y) := by
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
          have b5e62 : y = (M.op x y) ∨ y = (k x y) := by grind
          clear b5e60
          have b5e63 : y = (k x y) := by
            first
            | (have r₁ := b5e62
               have r₂ := b5e21
               grind)
            | exact resolve b5e62 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e62
          have b5e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e1383 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e67 x y
               grind)
            | exact superpose b5e67 b5e24
            | (have j1 := b5e67 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e67 x y
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e67 y x
               grind)
            | exact resolve b5e24 b5e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e67
          have b5e1413 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e1383
          have b5e1420 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b5e1413
               have r₂ := b5e23
               grind)
            | exact resolve b5e1413 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1413
          have b5e1428 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1420
               have i₂ := b5e63
               grind)
            | exact superpose b5e63 b5e1420
            | exact resolve b5e1420 b5e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e63 b5e1420
          have b5e1429 : False := by grind
          exact b5e1429
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x y) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ (M.op x y)) ≠ (σ y) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e19
          | exact resolve b6e19 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
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
        have b6e37 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X2 X4) X5) = (M.op X2 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X4 X5
          first
          | (have i₁ := b6e12 X2 (M.op X0 x) X4 X5
             have i₂ := b6e12 X0 X1 x X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e40 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 (σ x))) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 (σ x) X0 (σ y) X1
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x x
             have i₂ := b6e12 X0 X2 x x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X4 X0)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X0 X4 X1 (M.op x (M.op X0 X1))
             have i₂ := b6e12 (M.op X0 X1) x X2 X3
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e46 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ X3 ∨ (M.op X0 X2) = (k (M.op X0 X2) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e15 (M.op X0 X2) X3
             have i₂ := b6e12 X0 X1 X2 X3
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 (M.op X0 X2) X3
             grind)
          | (have r₁ := b6e15 X3 (M.op (M.op X3 X2) X3)
             have r₂ := b6e12 X3 (M.op X3 X2) X2 X3
             grind)
          | (have r₁ := b6e15 (M.op X0 X2) (M.op X0 (M.op X1 X0))
             have r₂ := b6e12 X0 X1 X2 (M.op X0 (M.op X1 X0))
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by
          first
          | (have i₁ := b6e16 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e16
          | (have j0 := b6e16 (σ y) (σ x)
             grind)
          | (have r₁ := b6e16 (σ y) (σ x)
             have r₂ := b6e22
             grind)
          | exact resolve b6e16 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e50 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) := by grind
        clear b6e47
        have b6e51 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e50
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e50
          | exact resolve b6e50 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50
        have b6e58 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b6e60 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
        have b6e63 : x = (M.op x y) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e60
             have r₂ := b6e21
             grind)
          | exact resolve b6e60 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60
        have b6e66 : x = (M.op x y) := by
          first
          | (have r₁ := b6e63
             have r₂ := b6e20
             grind)
          | exact resolve b6e63 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e63
        have b6e68 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e23
             have i₂ := b6e66
             grind)
          | exact superpose b6e66 b6e23
          | exact resolve b6e23 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23
        have b6e71 : ∀ X0 X1 : G, (M.op x (M.op X0 x)) = (M.op x X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 x X0 y X1
             have i₂ := b6e66
             grind)
          | exact superpose b6e66 b6e12
          | exact resolve b6e12 b6e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e200 : ∀ X0 X2 : G, (M.op x X0) = (M.op x X2) := by
          intro X0 X2
          first
          | (have i₁ := b6e71 x X2
             have i₂ := b6e71 x X0
             grind)
          | (have i₁ := b6e71 X0 x
             have i₂ := b6e71 X0 (M.op X0 x)
             grind)
          | exact superpose b6e71 b6e71
          | exact resolve b6e71 b6e71
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e71
        have b6e312 : ∀ X0 : G, x = (M.op x X0) := by
          intro X0
          first
          | (have i₁ := b6e66
             have i₂ := b6e200 y X0
             grind)
          | (have i₁ := b6e66
             have i₂ := b6e200 X0 y
             grind)
          | exact superpose b6e200 b6e66
          | exact resolve b6e66 b6e200
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e66 b6e200
        have b6e477 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 x) := by
          intro X0 X1
          first
          | (have i₁ := b6e43 X0 X1 x
             have i₂ := b6e312 X0
             grind)
          | exact superpose b6e312 b6e43
          | exact resolve b6e43 b6e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e483 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) x) := by
          intro X0
          first
          | (have i₁ := b6e40 x X0
             have i₂ := b6e312 (σ x)
             grind)
          | exact superpose b6e312 b6e40
          | exact resolve b6e40 b6e312
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e312
        have b6e719 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ x)
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e15
          | (have j0 := b6e15 (σ y) (σ x)
             grind)
          | (have r₁ := b6e15 (σ y) (σ x)
             have r₂ := b6e51
             grind)
          | exact resolve b6e15 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e722 : ∀ X0 X1 X2 : G, (M.op (σ x) X0) = (M.op (σ y) (M.op X1 (M.op X2 X1))) ∨ (σ x) = (σ (k y x)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e37 X1 X2 (σ y) (σ x) X0
             have i₂ := b6e51
             grind)
          | exact superpose b6e51 b6e37
          | exact resolve b6e37 b6e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37
        have b6e729 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) := by grind
        clear b6e719
        have b6e734 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) x) ∨ (σ x) = (σ (k y x)) := by
          intro X0
          first
          | (have i₁ := b6e722 X0 x x
             have i₂ := b6e483 (M.op x (M.op x x))
             grind)
          | exact superpose b6e483 b6e722
          | exact resolve b6e722 b6e483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e722
        have b6e736 : (σ x) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e729
             have i₂ := b6e18 y x
             grind)
          | exact superpose b6e18 b6e729
          | exact resolve b6e729 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e729
        have b6e878 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
          intro X0 X1 X2
          first
          | (have j0 := b6e46 X0 X1 X1 (M.op X0 (M.op X2 X0))
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46
        have b6e879 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 x)) := by
          intro X0 X1
          first
          | (have i₁ := b6e878 X0 X1 x
             have i₂ := b6e477 X0 x
             grind)
          | exact superpose b6e477 b6e878
          | exact resolve b6e878 b6e477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e878
        have b6e2236 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e58 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58
        have b6e2238 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b6e2236 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2236
        have b6e2409 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X0))) = (M.op X2 x) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e477 X2 (M.op (M.op X0 x) x)
             have i₂ := b6e44 X0 x x X2 X1
             grind)
          | exact superpose b6e44 b6e477
          | exact resolve b6e477 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e2527 : ∀ X0 X2 : G, (M.op X2 x) = (M.op X2 (M.op X0 x)) := by
          intro X0 X2
          first
          | (have i₁ := b6e2409 X0 x X2
             have i₂ := b6e477 X0 x
             grind)
          | exact superpose b6e477 b6e2409
          | exact resolve b6e2409 b6e477
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e477 b6e2409
        have b6e9228 : (τ (σ x)) = (k y x) ∨ (σ y) = (σ (k y x)) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e736
             grind)
          | exact superpose b6e736 b6e13
          | exact resolve b6e13 b6e736
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e736
        have b6e9243 : (σ y) = (σ (k y x)) ∨ x = (k y x) := by
          first
          | (have i₁ := b6e9228
             have i₂ := b6e13 x
             grind)
          | exact superpose b6e13 b6e9228
          | exact resolve b6e9228 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9228
        have b6e23971 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e9243
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e9243
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e9243 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e9243
        have b6e23993 : (σ y) = (σ (M.op y x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
        clear b6e23971
        have b6e24012 : (σ y) = (σ (M.op y x)) ∨ y = (M.op x y) := by
          first
          | (have r₁ := b6e23993
             have r₂ := b6e21
             grind)
          | exact resolve b6e23993 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e23993
        have b6e24015 : (σ y) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e24012
             have r₂ := b6e20
             grind)
          | exact resolve b6e24012 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24012
        have b6e24033 : (M.op y x) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (M.op y x)
             have i₂ := b6e24015
             grind)
          | exact superpose b6e24015 b6e13
          | exact resolve b6e13 b6e24015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e24070 : y = (M.op y x) := by
          first
          | (have i₁ := b6e24033
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e24033
          | exact resolve b6e24033 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24033
        have b6e24413 : ∀ X0 : G, (M.op X0 x) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b6e2527 y X0
             have i₂ := b6e24070
             grind)
          | exact superpose b6e24070 b6e2527
          | exact resolve b6e2527 b6e24070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2527
        have b6e24458 : y = (k y y) := by
          first
          | (have i₁ := b6e879 y x
             have i₂ := b6e24070
             grind)
          | exact superpose b6e24070 b6e879
          | exact resolve b6e879 b6e24070
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e879 b6e24070
        have b6e25055 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e2238 y
             have i₂ := b6e24458
             grind)
          | exact superpose b6e24458 b6e2238
          | (have j0 := b6e2238 y
             grind)
          | exact resolve b6e2238 b6e24458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2238 b6e24458
        have b6e25058 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear b6e25055
        have b6e25060 : (σ y) = (M.op (σ x) x) := by
          first
          | (have i₁ := b6e25058
             have i₂ := b6e483 (σ y)
             grind)
          | exact superpose b6e483 b6e25058
          | exact resolve b6e25058 b6e483
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25058
        have b6e25061 : (σ y) = (M.op (σ x) y) := by
          first
          | (have i₁ := b6e25060
             have i₂ := b6e24413 (σ x)
             grind)
          | exact superpose b6e24413 b6e25060
          | exact resolve b6e25060 b6e24413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25060
        have b6e25506 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op (σ x) X0) = (M.op (σ x) x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e734 X0
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e734
          | (have j0 := b6e734 X0
             have j1 := b6e17 y x
             grind)
          | exact resolve b6e734 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e734
        have b6e25780 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op (σ x) X0) = (M.op (σ x) x) ∨ x = (M.op y x) := by
          intro X0
          first
          | (have j0 := b6e25506 X0
             grind)
          | (have r₁ := b6e25506 X0
             have r₂ := b6e20
             grind)
          | exact resolve b6e25506 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25506
        have b6e25841 : ∀ X0 : G, (σ x) = (σ (M.op y x)) ∨ (M.op (σ x) X0) = (M.op (σ x) x) := by
          intro X0
          first
          | (have j0 := b6e25780 X0
             grind)
          | (have r₁ := b6e25780 X0
             have r₂ := b6e21
             grind)
          | exact resolve b6e25780 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25780
        have b6e25875 : ∀ X0 : G, (σ x) = (σ y) ∨ (M.op (σ x) X0) = (M.op (σ x) x) := by
          intro X0
          first
          | (have i₁ := b6e25841 X0
             have i₂ := b6e24015
             grind)
          | exact superpose b6e24015 b6e25841
          | (have j0 := b6e25841 X0
             grind)
          | exact resolve b6e25841 b6e24015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25841
        have b6e25885 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) x) := by
          intro X0
          first
          | (have j0 := b6e25875 X0
             grind)
          | (have r₁ := b6e25875 X0
             have r₂ := b6e68
             grind)
          | exact resolve b6e25875 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25875
        have b6e25889 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) y) := by
          intro X0
          first
          | (have i₁ := b6e25885 X0
             have i₂ := b6e24413 (σ x)
             grind)
          | exact superpose b6e24413 b6e25885
          | exact resolve b6e25885 b6e24413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24413 b6e25885
        have b6e25891 : ∀ X0 : G, (σ y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b6e25889 X0
             have i₂ := b6e25061
             grind)
          | exact superpose b6e25061 b6e25889
          | exact resolve b6e25889 b6e25061
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25061 b6e25889
        have b6e25952 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e483 X0
             have i₂ := b6e25891 x
             grind)
          | exact superpose b6e25891 b6e483
          | exact resolve b6e483 b6e25891
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e483 b6e25891
        have b6e28313 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
          first
          | (have i₁ := b6e51
             have i₂ := b6e25952 (σ x)
             grind)
          | exact superpose b6e25952 b6e51
          | exact resolve b6e51 b6e25952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e51 b6e25952
        have b6e28530 : (σ x) = (σ (k y x)) := by
          first
          | (have r₁ := b6e28313
             have r₂ := b6e68
             grind)
          | exact resolve b6e28313 b6e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28313
        have b6e29170 : (σ x) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
          first
          | (have i₁ := b6e28530
             have i₂ := b6e17 y x
             grind)
          | exact superpose b6e17 b6e28530
          | (have j1 := b6e17 y x
             grind)
          | exact resolve b6e28530 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28530
        have b6e29215 : (σ x) = (σ (M.op y x)) ∨ x = (M.op y x) := by
          first
          | (have r₁ := b6e29170
             have r₂ := b6e20
             grind)
          | exact resolve b6e29170 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29170
        have b6e29220 : (σ x) = (σ (M.op y x)) := by
          first
          | (have r₁ := b6e29215
             have r₂ := b6e21
             grind)
          | exact resolve b6e29215 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29215
        have b6e29225 : (σ x) = (σ y) := by
          first
          | (have i₁ := b6e29220
             have i₂ := b6e24015
             grind)
          | exact superpose b6e24015 b6e29220
          | exact resolve b6e29220 b6e24015
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e24015 b6e29220
        have b6e29226 : False := by grind
        exact b6e29226
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x y) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e52 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e55 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e52
          have b7e56 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e55
               have r₂ := b7e23
               grind)
            | exact resolve b7e55 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e55
          have b7e57 : (σ y) = (σ (k x y)) := by
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
          have b7e60 : (τ (σ y)) = (k x y) := by
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
          have b7e61 : y = (k x y) := by
            first
            | (have i₁ := b7e60
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e60
            | exact resolve b7e60 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e60
          have b7e80 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e61
               grind)
            | exact superpose b7e61 b7e18
            | (have j0 := b7e18 y x
               grind)
            | exact resolve b7e18 b7e61
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e61
          have b7e81 : y = (M.op x y) ∨ x = (M.op y x) := by grind
          clear b7e80
          have b7e83 : x = (M.op y x) := by
            first
            | (have r₁ := b7e81
               have r₂ := b7e21
               grind)
            | exact resolve b7e81 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e81
          have b7e85 : False := by grind
          exact b7e85
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x y) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e1003 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e52 x y
               grind)
            | exact superpose b8e52 b8e24
            | (have j1 := b8e52 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e52 x y
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e52 y x
               grind)
            | exact resolve b8e24 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e1038 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b8e1003
          have b8e1045 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have r₁ := b8e1038
               have r₂ := b8e23
               grind)
            | exact resolve b8e1038 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1038
          have b8e1053 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1045
               grind)
            | exact superpose b8e1045 b8e20
            | exact resolve b8e20 b8e1045
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1045
          have b8e1770 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e1053
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1053
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1053 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1053
          have b8e1771 : x = (M.op y x) ∨ y = (M.op x y) := by grind
          clear b8e1770
          have b8e1772 : y = (M.op x y) := by
            first
            | (have r₁ := b8e1771
               have r₂ := b8e22
               grind)
            | exact resolve b8e1771 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1771
          have b8e1773 : False := by grind
          exact b8e1773

/-- `Equation4444`: `x ◇ (y ◇ x) = (y ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4444 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4444 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4444.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
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
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
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
      have b0e37 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
      have b0e38 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e44 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e11
        | exact resolve b0e11 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e44 X0 x
           have i₂ := b0e11 y x x
           grind)
        | exact superpose b0e11 b0e44
        | exact resolve b0e44 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e44
      have b0e46 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e45 X0
           have i₂ := b0e38 (M.op x y)
           grind)
        | exact superpose b0e38 b0e45
        | exact resolve b0e45 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e62 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X2
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op X2 X1)
           have i₂ := b0e16 (M.op X2 X1) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X1 X0) X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e68 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X2) ∨ (k X2 (M.op X0 X1)) = (M.op X2 (M.op X0 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 X1)
           have i₂ := b0e16 X2 (M.op X0 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X2 (M.op X0 X1)
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e69 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (σ x) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e20
           have i₂ := b0e16 X0 (σ x)
           grind)
        | exact superpose b0e16 b0e20
        | (have j1 := b0e16 X0 (σ x)
           grind)
        | exact resolve b0e20 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
      have b0e77 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e15 X0 (M.op x y)
           have i₂ := b0e46 (M.op x y)
           grind)
        | exact superpose b0e46 b0e15
        | (have j0 := b0e15 X0 (M.op x y)
           grind)
        | (have r₁ := b0e15 X0 (M.op x y)
           have r₂ := b0e46 (M.op x y)
           grind)
        | exact resolve b0e15 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e80 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op x y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op x y)
           have i₂ := b0e46 (M.op X1 X0)
           grind)
        | exact superpose b0e46 b0e11
        | exact resolve b0e11 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e81 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ (k X0 (M.op x y)) = X0 := by
        intro X0
        first
        | (have j0 := b0e77 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
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
      have b0e101 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e80 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e80
        | exact resolve b0e80 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e80
      have b0e111 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e37 X1
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e37
        | exact resolve b0e37 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e117 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e37 X0
           grind)
        | exact superpose b0e37 b0e18
        | exact resolve b0e18 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e121 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (σ y) X0) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e16 (σ y) X0
           have i₂ := b0e37 (σ y)
           grind)
        | exact superpose b0e37 b0e16
        | (have j0 := b0e16 X0 X0
           grind)
        | exact resolve b0e16 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e134 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e121 X0
           have i₂ := b0e101
           grind)
        | exact superpose b0e101 b0e121
        | (have j0 := b0e121 X0
           grind)
        | exact resolve b0e121 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e121
      have b0e177 : ∀ X0 : G, (M.op x y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e46 (σ y)
           have i₂ := b0e111 (M.op x y) X0
           grind)
        | (have i₁ := b0e46 (σ y)
           have i₂ := b0e111 X0 (M.op x y)
           grind)
        | exact superpose b0e111 b0e46
        | exact resolve b0e46 b0e111
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e111
      have b0e435 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e117 (M.op x y)
           have i₂ := b0e46 (σ y)
           grind)
        | exact superpose b0e46 b0e117
        | exact resolve b0e117 b0e46
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e117
      have b0e931 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X0) = X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        grind
      clear b0e61
      have b0e1125 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e92
      have b0e1137 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1125 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1125
        | exact resolve b0e1125 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1125
      have b0e1381 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e62 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1382 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e62 X0 X1 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e2607 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e63 X0 (σ x) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e63
        | (have j0 := b0e63 X0 x x
           grind)
        | exact resolve b0e63 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e2614 : ∀ X0 : G, (M.op y X0) = (k y X0) ∨ (M.op x y) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e63 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e63
        | (have j0 := b0e63 X0 x x
           grind)
        | exact resolve b0e63 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e63
      have b0e2751 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2614 X0
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e2614
        | (have j0 := b0e2614 X0
           grind)
        | exact resolve b0e2614 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2614
      have b0e2758 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2607 X0
           have i₂ := b0e177 X0
           grind)
        | exact superpose b0e177 b0e2607
        | (have j0 := b0e2607 X0
           grind)
        | exact resolve b0e2607 b0e177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2607
      have b0e2879 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e2758 X0
           have i₂ := b0e101
           grind)
        | exact superpose b0e101 b0e2758
        | (have j0 := b0e2758 X0
           grind)
        | exact resolve b0e2758 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2758
      have b0e3166 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e70 x x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e70
        | exact resolve b0e70 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e70
      have b0e3379 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
      clear b0e3166
      have b0e4383 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e68 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e68
        | exact resolve b0e68 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e68
      have b0e5001 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ (k X0 (M.op x y)) = X0 := by
        intro X0
        grind
      clear b0e81
      have b0e5090 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
        intro X0
        first
        | (have j0 := b0e5001 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5001
      have b0e6081 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e931 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e931
      have b0e6083 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e6081 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6081
      have b0e6283 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e1381 y x
           have i₂ := b0e38 x
           grind)
        | exact superpose b0e38 b0e1381
        | (have j0 := b0e1381 y x
           grind)
        | exact resolve b0e1381 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1381
      have b0e6285 : y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have j1 := b0e4383 y
           grind)
        | (have r₁ := b0e6283
           have r₂ := b0e4383 x
           grind)
        | exact resolve b0e6283 b0e4383
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e4383 b0e6283
      have b0e6301 : y = (M.op x y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e6285
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e6285
        | exact resolve b0e6285 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6285
      have b0e6309 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e6301
           have i₂ := b0e38 y
           grind)
        | exact superpose b0e38 b0e6301
        | exact resolve b0e6301 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6301
      have b0e6368 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (k (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e1382 X0 (σ y)
           have i₂ := b0e177 X0
           grind)
        | exact superpose b0e177 b0e1382
        | (have j0 := b0e1382 X0 x
           grind)
        | (have r₁ := b0e1382 (M.op x y) (σ y)
           have r₂ := b0e177 (M.op x y)
           grind)
        | exact resolve b0e1382 b0e177
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e177
      have b0e6375 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e1382 X0 y
           have i₂ := b0e38 X0
           grind)
        | exact superpose b0e38 b0e1382
        | (have j0 := b0e1382 X0 x
           grind)
        | (have r₁ := b0e1382 (M.op x y) y
           have r₂ := b0e38 (M.op x y)
           grind)
        | exact resolve b0e1382 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e1382
      have b0e6382 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e6375 X0
           have j1 := b0e2751 X0
           grind)
        | (have r₁ := b0e6375 (k y X0)
           have r₂ := b0e2751 X0
           grind)
        | (have r₁ := b0e6375 (M.op (M.op x y) (M.op x y))
           have r₂ := b0e2751 (M.op x y)
           grind)
        | (have r₁ := b0e6375 X0
           have r₂ := b0e2751 X0
           grind)
        | exact resolve b0e6375 b0e2751
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2751 b0e6375
      have b0e6386 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op x y) = (k (σ y) X0) := by
        intro X0
        first
        | (have j0 := b0e6368 X0
           have j1 := b0e2879 X0
           grind)
        | (have r₁ := b0e6368 (k (σ y) X0)
           have r₂ := b0e2879 X0
           grind)
        | (have r₁ := b0e6368 (M.op (M.op x y) (M.op x y))
           have r₂ := b0e2879 (M.op x y)
           grind)
        | (have r₁ := b0e6368 X0
           have r₂ := b0e2879 X0
           grind)
        | exact resolve b0e6368 b0e2879
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e2879 b0e6368
      have b0e7992 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e6083 X0
           have i₂ := b0e6382 X0
           grind)
        | exact superpose b0e6382 b0e6083
        | (have j0 := b0e6083 X0
           have j1 := b0e6382 X0
           grind)
        | (have r₁ := b0e6083 X0
           have r₂ := b0e6382 X0
           grind)
        | exact resolve b0e6083 b0e6382
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6083 b0e6382
      have b0e8058 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e7992 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e7992
      have b0e14790 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e1137 X0
           have i₂ := b0e6386 (σ X0)
           grind)
        | exact superpose b0e6386 b0e1137
        | (have j1 := b0e6386 (σ X0)
           grind)
        | exact resolve b0e1137 b0e6386
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1137 b0e6386
      have b0e14872 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e14790 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e14790
        | (have j0 := b0e14790 X0
           grind)
        | exact resolve b0e14790 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14790
      have b0e14896 : ∀ X0 : G, (M.op x y) = (σ (k y X0)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e14872 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e14872
        | (have j0 := b0e14872 X0
           grind)
        | exact resolve b0e14872 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14872
      have b0e19987 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e14896 X0
           have i₂ := b0e8058 X0
           grind)
        | exact superpose b0e8058 b0e14896
        | (have j0 := b0e14896 X0
           have j1 := b0e8058 X0
           grind)
        | exact resolve b0e14896 b0e8058
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8058
      have b0e19991 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14896 y
           have i₂ := b0e6309
           grind)
        | exact superpose b0e6309 b0e14896
        | exact resolve b0e14896 b0e6309
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6309 b0e14896
      have b0e20179 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
      clear b0e19991
      have b0e20180 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e19987 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19987
      have b0e20254 : y = (M.op x y) := by
        first
        | (have r₁ := b0e20179
           have r₂ := b0e435
           grind)
        | exact resolve b0e20179 b0e435
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20179
      have b0e20258 : ∀ X0 : G, (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e20180 X0
           grind)
        | (have r₁ := b0e20180 X0
           have r₂ := b0e435
           grind)
        | exact resolve b0e20180 b0e435
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20180
      have b0e21225 : ∀ X0 : G, y = (M.op X0 y) := by
        intro X0
        first
        | (have i₁ := b0e46 X0
           have i₂ := b0e20254
           grind)
        | exact superpose b0e20254 b0e46
        | exact resolve b0e46 b0e20254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e46
      have b0e21236 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e435
           have i₂ := b0e20254
           grind)
        | exact superpose b0e20254 b0e435
        | exact resolve b0e435 b0e20254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e435
      have b0e21239 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b0e5090 X0
           have i₂ := b0e20254
           grind)
        | exact superpose b0e20254 b0e5090
        | exact resolve b0e5090 b0e20254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5090
      have b0e22213 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16 X0 X0
           have i₂ := b0e20258 X0
           grind)
        | exact superpose b0e20258 b0e16
        | (have j0 := b0e16 X0 X0
           grind)
        | exact resolve b0e16 b0e20258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e22241 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e134 (σ y)
           have i₂ := b0e20258 (σ y)
           grind)
        | exact superpose b0e20258 b0e134
        | (have j0 := b0e134 (σ y)
           grind)
        | exact resolve b0e134 b0e20258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134
      have b0e22251 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
        first
        | (have i₁ := b0e3379
           have i₂ := b0e20258 x
           grind)
        | exact superpose b0e20258 b0e3379
        | exact resolve b0e3379 b0e20258
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3379 b0e20258
      have b0e22260 : (σ x) = (σ y) := by grind
      clear b0e22251
      have b0e22264 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by grind
      clear b0e22241
      have b0e22282 : ∀ X0 : G, (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e22213 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22213
      have b0e22321 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e22264
           have i₂ := b0e37 (σ y)
           grind)
        | exact superpose b0e37 b0e22264
        | exact resolve b0e22264 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e22264
      have b0e22343 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) := by
        first
        | (have i₁ := b0e22321
           have i₂ := b0e101
           grind)
        | exact superpose b0e101 b0e22321
        | exact resolve b0e22321 b0e101
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e101 b0e22321
      have b0e22344 : (M.op x y) = (σ y) := by grind
      clear b0e22343
      have b0e22349 : (M.op x y) = (σ x) := by
        first
        | (have i₁ := b0e22344
           have i₂ := b0e22260
           grind)
        | exact superpose b0e22260 b0e22344
        | exact resolve b0e22344 b0e22260
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22260 b0e22344
      have b0e22351 : y = (σ x) := by
        first
        | (have i₁ := b0e22349
           have i₂ := b0e20254
           grind)
        | exact superpose b0e20254 b0e22349
        | exact resolve b0e22349 b0e20254
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20254 b0e22349
      have b0e22760 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y ∨ y = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e69 X0
           have i₂ := b0e22351
           grind)
        | exact superpose b0e22351 b0e69
        | exact resolve b0e69 b0e22351
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e22351
      have b0e22805 : ∀ X0 : G, (M.op X0 y) = (k X0 y) ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have j0 := b0e22760 X0
           grind)
        | (have r₁ := b0e22760 X0
           have r₂ := b0e21236
           grind)
        | exact resolve b0e22760 b0e21236
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22760
      have b0e22817 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e22805 X0
           have i₂ := b0e21239 X0
           grind)
        | exact superpose b0e21239 b0e22805
        | (have j0 := b0e22805 X0
           grind)
        | exact resolve b0e22805 b0e21239
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21239 b0e22805
      have b0e22822 : ∀ X0 : G, y = X0 ∨ (M.op X0 X0) = y := by
        intro X0
        first
        | (have i₁ := b0e22817 X0
           have i₂ := b0e21225 X0
           grind)
        | exact superpose b0e21225 b0e22817
        | (have j0 := b0e22817 X0
           grind)
        | exact resolve b0e22817 b0e21225
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21225 b0e22817
      have b0e22825 : ∀ X0 : G, y = X0 ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e22822 X0
           have i₂ := b0e22282 X0
           grind)
        | exact superpose b0e22282 b0e22822
        | (have j0 := b0e22822 X0
           grind)
        | exact resolve b0e22822 b0e22282
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22282 b0e22822
      have b0e22826 : ∀ X0 : G, y = X0 := by
        intro X0
        first
        | (have j0 := b0e22825 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22825
      have b0e23218 : y ≠ y := by
        first
        | (have i₁ := b0e21236
           have i₂ := b0e22826 (σ y)
           grind)
        | exact superpose b0e22826 b0e21236
        | (have r₁ := b0e21236
           have r₂ := b0e22826 (σ y)
           grind)
        | exact resolve b0e21236 b0e22826
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21236 b0e22826
      have b0e23379 : False := by grind
      exact b0e23379
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
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
        have b1e39 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e40 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e39 X0
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e39
          | exact resolve b1e39 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e46 : ∀ X0 X1 : G, (M.op y X0) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e40 X1
             have i₂ := b1e40 X0
             grind)
          | exact superpose b1e40 b1e40
          | exact resolve b1e40 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 X1 : G, (M.op y (M.op y X0)) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 y x x
             have i₂ := b1e40 X0
             grind)
          | exact superpose b1e40 b1e12
          | exact resolve b1e12 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e50 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op y X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e47 X0 X1
             have i₂ := b1e40 (M.op y X0)
             grind)
          | exact superpose b1e40 b1e47
          | exact resolve b1e47 b1e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e88 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b1e91 : y = (M.op y y) := by grind
        clear b1e88
        have b1e123 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e91
             have i₂ := b1e46 y X0
             grind)
          | (have i₁ := b1e91
             have i₂ := b1e46 X0 y
             grind)
          | exact superpose b1e46 b1e91
          | exact resolve b1e91 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e91
        have b1e126 : ∀ X0 X1 X2 : G, (M.op X1 (M.op y X0)) = (M.op (M.op y X0) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b1e12 X0 y X2
             have i₂ := b1e46 X0 X1
             grind)
          | (have i₁ := b1e12 X1 y X2
             have i₂ := b1e46 X0 X1
             grind)
          | exact superpose b1e46 b1e12
          | exact resolve b1e12 b1e46
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e127 : ∀ X0 X1 : G, (M.op x y) = (M.op X1 (M.op y X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e126 X0 X1 x
             have i₂ := b1e50 X0 x
             grind)
          | exact superpose b1e50 b1e126
          | exact resolve b1e126 b1e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e50 b1e126
        have b1e129 : ∀ X1 : G, (M.op x y) = (M.op X1 y) := by
          intro X1
          first
          | (have i₁ := b1e127 x X1
             have i₂ := b1e123 x
             grind)
          | exact superpose b1e123 b1e127
          | exact resolve b1e127 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e127
        have b1e145 : y = (M.op x y) := by
          first
          | (have i₁ := b1e40 x
             have i₂ := b1e123 x
             grind)
          | exact superpose b1e123 b1e40
          | exact resolve b1e40 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e148 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y x
             have i₂ := b1e123 X0
             grind)
          | exact superpose b1e123 b1e12
          | exact resolve b1e12 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e150 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e148 X0 x
             have i₂ := b1e123 x
             grind)
          | exact superpose b1e123 b1e148
          | exact resolve b1e148 b1e123
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e123 b1e148
        have b1e237 : y = (σ y) := by
          first
          | (have i₁ := b1e43 y
             have i₂ := b1e150 (σ y)
             grind)
          | exact superpose b1e150 b1e43
          | exact resolve b1e43 b1e150
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43 b1e150
        have b1e380 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e237
             grind)
          | exact superpose b1e237 b1e19
          | exact resolve b1e19 b1e237
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e385 : (M.op x y) ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b1e380
             have i₂ := b1e129 (σ x)
             grind)
          | exact superpose b1e129 b1e380
          | exact resolve b1e380 b1e129
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e129 b1e380
        have b1e386 : y ≠ (σ y) := by
          first
          | (have i₁ := b1e385
             have i₂ := b1e145
             grind)
          | exact superpose b1e145 b1e385
          | exact resolve b1e385 b1e145
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e145 b1e385
        have b1e387 : False := by grind
        exact b1e387
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
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
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 X0 X3
             have i₂ := b2e12 X1 X0 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e12 x x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e33 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          grind
        have b2e38 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : ∀ X0 : G, (M.op y (M.op x y)) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e38 X0 x
             have i₂ := b2e12 y x x
             grind)
          | exact superpose b2e12 b2e38
          | exact resolve b2e38 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38
        have b2e41 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
          intro X0
          first
          | (have i₁ := b2e39 X0
             have i₂ := b2e29 (M.op x y)
             grind)
          | exact superpose b2e29 b2e39
          | exact resolve b2e39 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e39
        have b2e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b2e182 : ∀ X0 X1 X2 : G, (M.op x y) = (M.op (M.op X0 X1) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e27 X0 X1 (M.op x y) X2
             have i₂ := b2e41 (M.op X0 X1)
             grind)
          | exact superpose b2e41 b2e27
          | exact resolve b2e27 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e1756 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e71 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e1757 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e1756
             have r₂ := b2e22
             grind)
          | exact resolve b2e1756 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1756
        have b2e1758 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e1757
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e1757
          | exact resolve b2e1757 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1757
        have b2e1759 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e1758
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e1758
          | exact resolve b2e1758 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e1758
        have b2e1767 : ∀ X0 : G, (M.op x y) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e182 (σ x) (σ y) X0
             have i₂ := b2e1759
             grind)
          | exact superpose b2e1759 b2e182
          | exact resolve b2e182 b2e1759
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e182
        have b2e2463 : (M.op x y) ≠ (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1767 (σ x)
             grind)
          | exact superpose b2e1767 b2e21
          | exact resolve b2e21 b2e1767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e2464 : (M.op x y) = (σ x) := by
          first
          | (have i₁ := b2e1759
             have i₂ := b2e1767 (σ y)
             grind)
          | exact superpose b2e1767 b2e1759
          | exact resolve b2e1759 b2e1767
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1759 b2e1767
        have b2e2506 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b2e2463
             have i₂ := b2e2464
             grind)
          | exact superpose b2e2464 b2e2463
          | exact resolve b2e2463 b2e2464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2463
        have b2e2850 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
          intro X0
          first
          | (have i₁ := b2e41 X0
             have i₂ := b2e2464
             grind)
          | exact superpose b2e2464 b2e41
          | exact resolve b2e41 b2e2464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41
        have b2e2852 : ∀ X0 : G, (σ x) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b2e29 X0
             have i₂ := b2e2464
             grind)
          | exact superpose b2e2464 b2e29
          | exact resolve b2e29 b2e2464
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e2464
        have b2e3973 : ∀ X0 : G, (σ x) = (k (σ x) (M.op X0 (σ x))) := by
          intro X0
          first
          | (have i₁ := b2e33 X0 y
             have i₂ := b2e2852 X0
             grind)
          | exact superpose b2e2852 b2e33
          | exact resolve b2e33 b2e2852
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e2852
        have b2e3993 : (σ x) = (k (σ x) (σ x)) := by
          first
          | (have i₁ := b2e3973 x
             have i₂ := b2e2850 x
             grind)
          | exact superpose b2e2850 b2e3973
          | exact resolve b2e3973 b2e2850
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2850 b2e3973
        have b2e4009 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b2e3993
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e3993
          | exact resolve b2e3993 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e3993
        have b2e5120 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e4009
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e4009
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e4009 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4009
        have b2e5136 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b2e5120
        have b2e5150 : (σ x) = (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e5136
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5136
          | exact resolve b2e5136 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5136
        have b2e5159 : x = (M.op x x) := by
          first
          | (have r₁ := b2e5150
             have r₂ := b2e2506
             grind)
          | exact resolve b2e5150 b2e2506
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5150
        have b2e5168 : x = y := by
          first
          | (have i₁ := b2e5159
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e5159
          | exact resolve b2e5159 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e5159
        have b2e6246 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e2506
             have i₂ := b2e5168
             grind)
          | exact superpose b2e5168 b2e2506
          | exact resolve b2e2506 b2e5168
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2506 b2e5168
        have b2e6252 : False := by grind
        exact b2e6252
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
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
        have b3e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e39 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
        have b3e40 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 y y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e43 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e40 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e40
          | exact resolve b3e40 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e40
        have b3e47 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 y x
             have i₂ := b3e43 X0
             grind)
          | exact superpose b3e43 b3e12
          | exact resolve b3e12 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e48 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e47 X0 x
             have i₂ := b3e43 x
             grind)
          | exact superpose b3e43 b3e47
          | exact resolve b3e47 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e52 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e43 y
             grind)
          | exact superpose b3e43 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e43 y
             grind)
          | exact resolve b3e16 b3e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e52 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e48 (M.op X1 X0)
             grind)
          | exact superpose b3e48 b3e12
          | exact resolve b3e12 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e75 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 X1)
             have i₂ := b3e17 (M.op X2 X1) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X1 X0) X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e90 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X0) = X0 ∨ y = X0 := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e75 X0 X1 X2
             have i₂ := b3e59 X1 X2
             grind)
          | exact superpose b3e59 b3e75
          | (have j0 := b3e75 X0 X1 X2
             grind)
          | exact resolve b3e75 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e75
        have b3e99 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e59 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e59
          | exact resolve b3e59 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e104 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = y := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e59 X0 X1
             grind)
          | exact superpose b3e59 b3e12
          | exact resolve b3e12 b3e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
        have b3e116 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e99
             grind)
          | exact superpose b3e99 b3e19
          | exact resolve b3e19 b3e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e120 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e116
             have i₂ := b3e48 x
             grind)
          | exact superpose b3e48 b3e116
          | exact resolve b3e116 b3e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e48 b3e116
        have b3e134 : ∀ X0 : G, y = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e99
             have i₂ := b3e39 X0
             grind)
          | exact superpose b3e39 b3e99
          | exact resolve b3e99 b3e39
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e39 b3e99
        have b3e620 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e53
        have b3e638 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e620 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e620
        have b3e844 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0 y
             have i₂ := b3e638 (τ X0)
             grind)
          | exact superpose b3e638 b3e27
          | exact resolve b3e27 b3e638
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e638
        have b3e845 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e844 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e844
          | exact resolve b3e844 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e844
        have b3e1765 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b3e845 (M.op X0 X1)
             have i₂ := b3e90 (σ y) X1 X0
             grind)
          | exact superpose b3e90 b3e845
          | (have j1 := b3e90 (σ y) X1 x
             grind)
          | exact resolve b3e845 b3e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e90 b3e845
        have b3e1823 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have j0 := b3e1765 X0 X1
             grind)
          | (have r₁ := b3e1765 X0 X1
             have r₂ := b3e120
             grind)
          | exact resolve b3e1765 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1765
        have b3e1862 : ∀ X0 X1 : G, (M.op X0 X1) = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b3e1823 X0 X1
             have i₂ := b3e104 X1 X0 (σ y)
             grind)
          | exact superpose b3e104 b3e1823
          | exact resolve b3e1823 b3e104
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e104 b3e1823
        have b3e1868 : ∀ X0 X1 : G, y = (σ y) ∨ (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e1862 X0 X1
             have i₂ := b3e134 (σ y)
             grind)
          | exact superpose b3e134 b3e1862
          | (have j0 := b3e1862 X0 X1
             grind)
          | exact resolve b3e1862 b3e134
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e134 b3e1862
        have b3e1870 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
          intro X0 X1
          first
          | (have j0 := b3e1868 X0 X1
             grind)
          | (have r₁ := b3e1868 X0 X1
             have r₂ := b3e120
             grind)
          | exact resolve b3e1868 b3e120
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e120 b3e1868
        have b3e1938 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e1870 x x
             grind)
          | exact superpose b3e1870 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e1870 x x
             grind)
          | exact resolve b3e20 b3e1870
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1870
        have b3e1939 : False := by grind
        exact b3e1939
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e41 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
          have b4e42 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b4e45 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e42
            | exact resolve b4e42 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e46 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b4e41 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e41
            | exact resolve b4e41 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e50 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y x
               have i₂ := b4e45 X0
               grind)
            | exact superpose b4e45 b4e13
            | exact resolve b4e13 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e50 X0 x
               have i₂ := b4e45 x
               grind)
            | exact superpose b4e45 b4e50
            | exact resolve b4e50 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e50
          have b4e105 : y = (σ y) := by
            first
            | (have i₁ := b4e51 (σ y)
               have i₂ := b4e46 y
               grind)
            | exact superpose b4e46 b4e51
            | exact resolve b4e51 b4e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46
          have b4e130 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e105
               grind)
            | exact superpose b4e105 b4e20
            | exact resolve b4e20 b4e105
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e135 : y ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e130
               have i₂ := b4e51 (σ x)
               grind)
            | exact superpose b4e51 b4e130
            | exact resolve b4e130 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e130
          have b4e136 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e135
               have i₂ := b4e51 x
               grind)
            | exact superpose b4e51 b4e135
            | exact resolve b4e135 b4e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51 b4e135
          have b4e137 : False := by grind
          exact b4e137
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e37 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b5e44 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e37 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e37
            | exact resolve b5e37 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37
          have b5e46 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y X1) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y x
               have i₂ := b5e44 X0
               grind)
            | exact superpose b5e44 b5e13
            | exact resolve b5e13 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e47 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e46 X0 x
               have i₂ := b5e44 x
               grind)
            | exact superpose b5e44 b5e46
            | exact resolve b5e46 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46
          have b5e49 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e44 y
               grind)
            | exact superpose b5e44 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e44 y
               grind)
            | exact resolve b5e17 b5e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e44
          have b5e51 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e49 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e57 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y
               have i₂ := b5e47 (M.op X1 X0)
               grind)
            | exact superpose b5e47 b5e13
            | exact resolve b5e13 b5e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e47
          have b5e70 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X1 X2 (M.op X2 X1)
               have i₂ := b5e18 (M.op X2 X1) X0
               grind)
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e18 X0 (M.op (M.op X1 X0) X2)
               grind)
            | exact superpose b5e18 b5e13
            | (have j1 := b5e18 X0 X0
               grind)
            | exact resolve b5e13 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e71 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e23
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e23
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e23
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e23
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e23 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 X1 X2 : G, (k (M.op X2 X1) X0) = (M.op (M.op X2 X1) X0) ∨ (M.op X0 X0) = X0 ∨ y = X0 := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e70 X0 X1 X2
               have i₂ := b5e57 X1 X2
               grind)
            | exact superpose b5e57 b5e70
            | (have j0 := b5e70 X0 X1 X2
               grind)
            | exact resolve b5e70 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e70
          have b5e100 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = y := by
            intro X0 X1 X2
            first
            | (have i₁ := b5e13 X0 X1 X2
               have i₂ := b5e57 X0 X1
               grind)
            | exact superpose b5e57 b5e13
            | exact resolve b5e13 b5e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e57
          have b5e519 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e51
          have b5e539 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e519 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e519
          have b5e733 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e539 (τ X0)
               grind)
            | exact superpose b5e539 b5e27
            | exact resolve b5e27 b5e539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27
          have b5e734 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e733 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e733
            | exact resolve b5e733 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e733
          have b5e1048 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e71 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e71
          have b5e1049 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1048
               have r₂ := b5e24
               grind)
            | exact resolve b5e1048 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1048
          have b5e1050 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1049
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1049
            | exact resolve b5e1049 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1049
          have b5e1051 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e1050
               have i₂ := b5e539 x
               grind)
            | exact superpose b5e539 b5e1050
            | exact resolve b5e1050 b5e539
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e539 b5e1050
          have b5e1060 : ∀ X0 : G, y = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e100 (σ y) (σ x) X0
               have i₂ := b5e1051
               grind)
            | exact superpose b5e1051 b5e100
            | exact resolve b5e100 b5e1051
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1051
          have b5e1363 : y ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1060 (σ x)
               grind)
            | exact superpose b5e1060 b5e23
            | exact resolve b5e23 b5e1060
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1060
          have b5e1705 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
            intro X0 X1
            first
            | (have i₁ := b5e734 (M.op X0 X1)
               have i₂ := b5e87 (σ y) X1 X0
               grind)
            | exact superpose b5e87 b5e734
            | (have j1 := b5e87 (σ y) X1 x
               grind)
            | exact resolve b5e734 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87 b5e734
          have b5e1765 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) ∨ y = (σ y) := by
            intro X0 X1
            first
            | (have j0 := b5e1705 X0 X1
               grind)
            | (have r₁ := b5e1705 X0 X1
               have r₂ := b5e24
               grind)
            | exact resolve b5e1705 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1705
          have b5e1804 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X1) (σ y)) := by
            intro X0 X1
            first
            | (have j0 := b5e1765 X0 X1
               grind)
            | (have r₁ := b5e1765 X0 X1
               have r₂ := b5e1363
               grind)
            | exact resolve b5e1765 b5e1363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1363 b5e1765
          have b5e1812 : ∀ X0 X1 : G, (M.op X0 X1) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e1804 X0 X1
               have i₂ := b5e100 X1 X0 (σ y)
               grind)
            | exact superpose b5e100 b5e1804
            | exact resolve b5e1804 b5e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e100 b5e1804
          have b5e2490 : y ≠ y := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e1812 x x
               grind)
            | exact superpose b5e1812 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e1812 x x
               grind)
            | exact resolve b5e21 b5e1812
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1812
          have b5e2491 : False := by grind
          exact b5e2491
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X0) X2) := by
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
        have b6e46 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
          intro X0 X1
          grind
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
        have b6e97 : ∀ X0 : G, (M.op x X0) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e12 y x x
             have i₂ := b6e95
             grind)
          | exact superpose b6e95 b6e12
          | exact resolve b6e12 b6e95
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e202 : y ≠ (M.op y x) := by
          first
          | (have i₁ := b6e20
             have i₂ := b6e97 x
             grind)
          | exact superpose b6e97 b6e20
          | exact resolve b6e20 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e204 : x = (M.op y x) := by
          first
          | (have i₁ := b6e95
             have i₂ := b6e97 y
             grind)
          | exact superpose b6e97 b6e95
          | exact resolve b6e95 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e210 : ∀ X0 X1 : G, (M.op X0 (M.op y x)) = (M.op (M.op y x) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 x x
             have i₂ := b6e97 X0
             grind)
          | exact superpose b6e97 b6e12
          | exact resolve b6e12 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e211 : ∀ X0 : G, (M.op X0 (M.op y x)) = (M.op x (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e210 X0 x
             have i₂ := b6e12 x y x
             grind)
          | exact superpose b6e12 b6e210
          | exact resolve b6e210 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e210
        have b6e214 : x ≠ y := by
          first
          | (have i₁ := b6e202
             have i₂ := b6e204
             grind)
          | exact superpose b6e204 b6e202
          | exact resolve b6e202 b6e204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e202
        have b6e215 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e211 X0
             have i₂ := b6e97 (M.op y x)
             grind)
          | exact superpose b6e97 b6e211
          | exact resolve b6e211 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e211
        have b6e217 : ∀ X0 : G, x = (M.op X0 x) := by
          intro X0
          first
          | (have i₁ := b6e215 X0
             have i₂ := b6e204
             grind)
          | exact superpose b6e204 b6e215
          | exact resolve b6e215 b6e204
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e204 b6e215
        have b6e239 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) (M.op y x)) := by
          intro X0
          first
          | (have i₁ := b6e46 x X0
             have i₂ := b6e97 (M.op X0 x)
             grind)
          | exact superpose b6e97 b6e46
          | exact resolve b6e46 b6e97
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e46 b6e97
        have b6e240 : ∀ X0 : G, (M.op X0 x) = (k (M.op X0 x) x) := by
          intro X0
          first
          | (have i₁ := b6e239 X0
             have i₂ := b6e217 y
             grind)
          | exact superpose b6e217 b6e239
          | exact resolve b6e239 b6e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e239
        have b6e246 : x = (k x x) := by
          first
          | (have i₁ := b6e240 x
             have i₂ := b6e217 x
             grind)
          | exact superpose b6e217 b6e240
          | exact resolve b6e240 b6e217
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e217 b6e240
        have b6e2527 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
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
        have b6e2724 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e2527
        have b6e2784 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e2724
             have i₂ := b6e246
             grind)
          | exact superpose b6e246 b6e2724
          | exact resolve b6e2724 b6e246
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e246 b6e2724
        have b6e2785 : (σ x) = (σ y) := by grind
        clear b6e2784
        have b6e2839 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e2785
             grind)
          | exact superpose b6e2785 b6e13
          | exact resolve b6e13 b6e2785
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2785
        have b6e2853 : x = y := by
          first
          | (have i₁ := b6e2839
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e2839
          | exact resolve b6e2839 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2839
        have b6e2860 : False := by grind
        exact b6e2860
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
          have b7e90 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e93 : y = (M.op y y) := by grind
          clear b7e90
          have b7e97 : False := by grind
          exact b7e97
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
          have b8e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b8e961 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e61 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e962 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e961
               have r₂ := b8e24
               grind)
            | exact resolve b8e961 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e961
          have b8e963 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e962
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e962
            | exact resolve b8e962 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e962
          have b8e964 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e963
               grind)
            | exact superpose b8e963 b8e20
            | exact resolve b8e20 b8e963
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e963
          have b8e981 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e964
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e964
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e964 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e964
          have b8e982 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e981
          have b8e985 : y = (M.op y y) := by
            first
            | (have r₁ := b8e982
               have r₂ := b8e21
               grind)
            | exact resolve b8e982 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e982
          have b8e988 : False := by grind
          exact b8e988

/-- `Equation4447`: `x ◇ (y ◇ x) = (y ◇ y) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_y_x_x_pxy_Equation4447 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4447 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4447.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
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
      have b0e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
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
      have b0e36 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
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
      have b0e40 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 (σ x) X1
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 x X1
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e64 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X1)) = (M.op X0 X3) ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e11 X1 X2 X3
           have i₂ := b0e16 X2 X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X1)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e66 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 X2) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X0 X2
           have i₂ := b0e16 X0 X1
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op X1 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e67 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X2) X0) = (M.op (M.op X2 X2) X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op X2 X2)
           have i₂ := b0e16 (M.op X2 X2) X0
           grind)
        | (have i₁ := b0e11 X0 X1 X2
           have i₂ := b0e16 X0 (M.op (M.op X1 X1) X2)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 X0
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e73 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X2 X2) ∨ (k X2 (M.op X0 X0)) = (M.op X2 (M.op X0 X0)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X0 (M.op X0 X0)
           have i₂ := b0e16 X2 (M.op X0 X0)
           grind)
        | exact superpose b0e16 b0e11
        | (have j1 := b0e16 X0 (M.op X1 (M.op X0 X1))
           grind)
        | exact resolve b0e11 b0e16
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e91 : ∀ X0 X1 X2 : G, (M.op y X0) = (M.op X1 (M.op X2 X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X1 X2 (M.op x (M.op X2 X2))
           have i₂ := b0e41 (M.op X2 X2) X0
           grind)
        | exact superpose b0e41 b0e11
        | exact resolve b0e11 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e93 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x X0)) := by
        intro X0
        first
        | (have i₁ := b0e36 x
           have i₂ := b0e41 X0 x
           grind)
        | (have i₁ := b0e36 (M.op x y)
           have i₂ := b0e41 y x
           grind)
        | exact superpose b0e41 b0e36
        | exact resolve b0e36 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41
      have b0e96 : ∀ X1 X2 : G, (M.op x y) = (M.op X1 (M.op X2 X1)) := by
        intro X1 X2
        first
        | (have i₁ := b0e91 x X1 X2
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e91
        | exact resolve b0e91 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e91
      have b0e113 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e134 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e35 X1
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e35
        | exact resolve b0e35 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e140 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e18
        | exact resolve b0e18 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e148 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (σ y) X0 X1
           have i₂ := b0e35 (M.op X0 (σ y))
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149 : (M.op x y) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e93 (σ y)
           have i₂ := b0e35 (M.op x (σ y))
           grind)
        | exact superpose b0e35 b0e93
        | exact resolve b0e93 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e152 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e148 X0 X1
           have i₂ := b0e149
           grind)
        | exact superpose b0e149 b0e148
        | exact resolve b0e148 b0e149
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148 b0e149
      have b0e339 : ∀ X0 : G, (M.op x y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e93 (σ y)
           have i₂ := b0e134 (M.op x (σ y)) X0
           grind)
        | (have i₁ := b0e93 (σ y)
           have i₂ := b0e134 X0 (M.op x (σ y))
           grind)
        | exact superpose b0e134 b0e93
        | exact resolve b0e93 b0e134
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e134
      have b0e719 : (M.op x y) ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e140 (M.op x (σ y))
           have i₂ := b0e93 (σ y)
           grind)
        | exact superpose b0e93 b0e140
        | exact resolve b0e140 b0e93
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e93 b0e140
      have b0e3336 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
        intro X0
        grind
      clear b0e113
      have b0e3348 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
        intro X0
        first
        | (have i₁ := b0e3336 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e3336
        | exact resolve b0e3336 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3336
      have b0e3730 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
        intro X0 X1
        first
        | (have j0 := b0e66 X0 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e66
      have b0e5298 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e64 X0 X1 X2 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e64
      have b0e5307 : ∀ X0 X2 : G, (M.op x y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k X2 X0) = (M.op X2 X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e5298 X0 x X2
           have i₂ := b0e96 x X2
           grind)
        | exact superpose b0e96 b0e5298
        | (have j0 := b0e5298 X0 x X2
           grind)
        | (have r₁ := b0e5298 (M.op x y) x X2
           have r₂ := b0e96 x X2
           grind)
        | exact resolve b0e5298 b0e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5298
      have b0e8056 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have i₁ := b0e67 X0 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e67
        | (have j0 := b0e67 X0 x x
           grind)
        | exact resolve b0e67 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e8173 : ∀ X0 X2 : G, (M.op (σ y) X2) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (σ x) (σ x)) X0) = (k (M.op (σ x) (σ x)) X0) := by
        intro X0 X2
        first
        | (have i₁ := b0e40 x X2
           have i₂ := b0e67 X0 x (σ x)
           grind)
        | (have i₁ := b0e40 X0 x
           have i₂ := b0e67 (M.op X0 (M.op (σ x) X0)) x X2
           grind)
        | exact superpose b0e67 b0e40
        | (have j1 := b0e67 X0 x (σ x)
           grind)
        | exact resolve b0e40 b0e67
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e8359 : ∀ X0 : G, (M.op x y) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (σ x) (σ x)) X0) = (k (M.op (σ x) (σ x)) X0) := by
        intro X0
        first
        | (have i₁ := b0e8173 X0 x
           have i₂ := b0e339 x
           grind)
        | exact superpose b0e339 b0e8173
        | (have j0 := b0e8173 X0 x
           grind)
        | exact resolve b0e8173 b0e339
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8173
      have b0e8454 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op y X0) = (k y X0) := by
        intro X0
        first
        | (have j0 := b0e8056 X0
           have j1 := b0e5307 X0 y
           grind)
        | (have r₁ := b0e8056 X0
           have r₂ := b0e5307 X0 x
           grind)
        | (have r₁ := b0e8056 (M.op x y)
           have r₂ := b0e5307 (M.op x y) x
           grind)
        | (have r₁ := b0e8056 (M.op x y)
           have r₂ := b0e5307 (M.op (M.op x y) (M.op x y)) x
           grind)
        | exact resolve b0e8056 b0e5307
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8056
      have b0e8576 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (σ x) (σ x)) X0) = (k (M.op (σ x) (σ x)) X0) := by
        intro X0
        first
        | (have j0 := b0e8359 X0
           have j1 := b0e5307 X0 (M.op (σ x) (σ x))
           grind)
        | (have r₁ := b0e8359 X0
           have r₂ := b0e5307 X0 x
           grind)
        | (have r₁ := b0e8359 (M.op x y)
           have r₂ := b0e5307 (M.op x y) x
           grind)
        | (have r₁ := b0e8359 (M.op x y)
           have r₂ := b0e5307 (M.op (M.op x y) (M.op x y)) x
           grind)
        | exact resolve b0e8359 b0e5307
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5307 b0e8359
      have b0e8663 : ∀ X0 : G, (M.op x y) = (k y X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e8454 X0
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e8454
        | (have j0 := b0e8454 X0
           grind)
        | exact resolve b0e8454 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8454
      have b0e8744 : ∀ X0 : G, (M.op (σ y) X0) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e8576 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e8576
        | (have j0 := b0e8576 X0
           grind)
        | exact resolve b0e8576 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8576
      have b0e8832 : ∀ X0 : G, (M.op x y) = (k (σ y) X0) ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e8744 X0
           have i₂ := b0e339 X0
           grind)
        | exact superpose b0e339 b0e8744
        | (have j0 := b0e8744 X0
           grind)
        | exact resolve b0e8744 b0e339
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e339 b0e8744
      have b0e8956 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k y X0) := by
        intro X0
        grind
      clear b0e8663
      have b0e10577 : ∀ X0 : G, y = (M.op x y) ∨ (M.op X0 X0) = y ∨ (M.op X0 y) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b0e73 x x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e73
        | exact resolve b0e73 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e73
      have b0e11900 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e3348 X0
           have i₂ := b0e8832 (σ X0)
           grind)
        | exact superpose b0e8832 b0e3348
        | (have j1 := b0e8832 (σ X0)
           grind)
        | exact resolve b0e3348 b0e8832
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3348 b0e8832
      have b0e11919 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op x y) = (k (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b0e11900 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e11900
        | (have j0 := b0e11900 X0
           grind)
        | exact resolve b0e11900 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11900
      have b0e11966 : ∀ X0 : G, (M.op x y) = (σ (k y X0)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11919 X0
           have i₂ := b0e17 y X0
           grind)
        | exact superpose b0e17 b0e11919
        | (have j0 := b0e11919 X0
           grind)
        | exact resolve b0e11919 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11919
      have b0e13681 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e3730 y x
           have i₂ := b0e36 x
           grind)
        | exact superpose b0e36 b0e3730
        | (have j0 := b0e3730 y x
           grind)
        | exact resolve b0e3730 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e3730
      have b0e13685 : y = (M.op y y) ∨ (M.op y y) = (k y y) := by
        first
        | (have j1 := b0e10577 y
           grind)
        | (have r₁ := b0e13681
           have r₂ := b0e10577 x
           grind)
        | exact resolve b0e13681 b0e10577
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e10577 b0e13681
      have b0e13712 : y = (M.op x y) ∨ (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e13685
           have i₂ := b0e36 y
           grind)
        | exact superpose b0e36 b0e13685
        | exact resolve b0e13685 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e13685
      have b0e13725 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e13712
           have i₂ := b0e36 y
           grind)
        | exact superpose b0e36 b0e13712
        | exact resolve b0e13712 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36 b0e13712
      have b0e14328 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e11966 X0
           have i₂ := b0e8956 X0
           grind)
        | exact superpose b0e8956 b0e11966
        | (have j0 := b0e11966 X0
           have j1 := b0e8956 X0
           grind)
        | exact resolve b0e11966 b0e8956
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e8956
      have b0e14331 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e11966 y
           have i₂ := b0e13725
           grind)
        | exact superpose b0e13725 b0e11966
        | exact resolve b0e11966 b0e13725
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e11966 b0e13725
      have b0e14447 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
      clear b0e14331
      have b0e14448 : ∀ X0 : G, (M.op x y) = (σ (M.op x y)) ∨ (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e14328 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14328
      have b0e14490 : y = (M.op x y) := by
        first
        | (have r₁ := b0e14447
           have r₂ := b0e719
           grind)
        | exact resolve b0e14447 b0e719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14447
      have b0e14493 : ∀ X0 : G, (k X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e14448 X0
           grind)
        | (have r₁ := b0e14448 X0
           have r₂ := b0e719
           grind)
        | exact resolve b0e14448 b0e719
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14448
      have b0e14829 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e719
           have i₂ := b0e14490
           grind)
        | exact superpose b0e14490 b0e719
        | exact resolve b0e719 b0e14490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e719
      have b0e15725 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16 X0 X0
           have i₂ := b0e14493 X0
           grind)
        | exact superpose b0e14493 b0e16
        | (have j0 := b0e16 X0 X0
           grind)
        | exact resolve b0e16 b0e14493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e15742 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e67 (M.op X0 X0) X1 X0
           have i₂ := b0e14493 (M.op X0 X0)
           grind)
        | exact superpose b0e14493 b0e67
        | (have j0 := b0e67 (M.op X0 X0) X1 X0
           grind)
        | exact resolve b0e67 b0e14493
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e67 b0e14493
      have b0e15762 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e15742 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15742
      have b0e15775 : ∀ X0 : G, (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have j0 := b0e15725 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15725
      have b0e15805 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op x y) ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15762 X0 X1
           have i₂ := b0e152 X0 (M.op X0 X0)
           grind)
        | exact superpose b0e152 b0e15762
        | (have j0 := b0e15762 X0 X1
           grind)
        | exact resolve b0e15762 b0e152
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e152 b0e15762
      have b0e15816 : ∀ X0 X1 : G, (M.op X0 X0) = y ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15805 X0 X1
           have i₂ := b0e14490
           grind)
        | exact superpose b0e14490 b0e15805
        | (have j0 := b0e15805 X0 X1
           grind)
        | exact resolve b0e15805 b0e14490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15805
      have b0e15820 : ∀ X0 X1 : G, y = X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15816 X0 X1
           have i₂ := b0e15775 X0
           grind)
        | exact superpose b0e15775 b0e15816
        | (have j0 := b0e15816 X0 X1
           grind)
        | exact resolve b0e15816 b0e15775
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15816
      have b0e15822 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e15820 X0 x
           have i₂ := b0e96 x X0
           grind)
        | exact superpose b0e96 b0e15820
        | (have j0 := b0e15820 X0 x
           grind)
        | exact resolve b0e15820 b0e96
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96 b0e15820
      have b0e15824 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e15822 X0
           have i₂ := b0e14490
           grind)
        | exact superpose b0e14490 b0e15822
        | (have j0 := b0e15822 (M.op X0 X0)
           grind)
        | exact resolve b0e15822 b0e14490
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14490 b0e15822
      have b0e15826 : ∀ X0 : G, y = X0 ∨ y = X0 := by
        intro X0
        first
        | (have i₁ := b0e15824 X0
           have i₂ := b0e15775 X0
           grind)
        | exact superpose b0e15775 b0e15824
        | (have j0 := b0e15824 X0
           grind)
        | exact resolve b0e15824 b0e15775
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15775 b0e15824
      have b0e15827 : ∀ X0 : G, y = X0 := by
        intro X0
        first
        | (have j0 := b0e15826 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e15826
      have b0e16568 : y ≠ y := by
        first
        | (have i₁ := b0e14829
           have i₂ := b0e15827 (σ y)
           grind)
        | exact superpose b0e15827 b0e14829
        | (have r₁ := b0e14829
           have r₂ := b0e15827 (σ y)
           grind)
        | exact resolve b0e14829 b0e15827
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e14829 b0e15827
      have b0e16655 : False := by grind
      exact b0e16655
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
      · have b1e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
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
        have b1e37 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b1e12 (σ y) (σ y) x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e12
          | exact resolve b1e12 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e38 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e12 x x x
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e43 : ∀ X0 X1 : G, (M.op X0 (M.op x X0)) = (M.op y X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 x X1
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e12
          | exact resolve b1e12 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e47 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
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
        have b1e59 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 (σ y) X0 X1
             have i₂ := b1e47 (M.op X0 (σ y))
             grind)
          | exact superpose b1e47 b1e12
          | exact resolve b1e12 b1e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e89 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
        have b1e92 : y = (M.op y y) := by grind
        clear b1e89
        have b1e121 : ∀ X0 : G, (σ y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e47 (M.op x (σ y))
             have i₂ := b1e43 (σ y) X0
             grind)
          | exact superpose b1e43 b1e47
          | exact resolve b1e47 b1e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e139 : (M.op x y) = (σ y) := by
          first
          | (have i₁ := b1e38 x
             have i₂ := b1e121 x
             grind)
          | exact superpose b1e121 b1e38
          | exact resolve b1e38 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e38
        have b1e140 : y = (σ y) := by
          first
          | (have i₁ := b1e92
             have i₂ := b1e121 y
             grind)
          | exact superpose b1e121 b1e92
          | exact resolve b1e92 b1e121
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e92 b1e121
        have b1e148 : y = (M.op x y) := by
          first
          | (have i₁ := b1e139
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e139
          | exact resolve b1e139 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e139
        have b1e157 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b1e47 X0
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e47
          | exact resolve b1e47 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e47
        have b1e158 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e19
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e19
          | exact resolve b1e19 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e163 : (σ y) ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e158
             have i₂ := b1e148
             grind)
          | exact superpose b1e148 b1e158
          | exact resolve b1e158 b1e148
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e148 b1e158
        have b1e164 : y ≠ (M.op (σ x) y) := by
          first
          | (have i₁ := b1e163
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e163
          | exact resolve b1e163 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e163
        have b1e366 : ∀ X0 X1 : G, (M.op X0 y) = (M.op (M.op y y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b1e12 X0 y X1
             have i₂ := b1e157 X0
             grind)
          | exact superpose b1e157 b1e12
          | exact resolve b1e12 b1e157
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e157
        have b1e371 : ∀ X0 : G, (σ y) = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e366 X0 x
             have i₂ := b1e59 y x
             grind)
          | exact superpose b1e59 b1e366
          | exact resolve b1e366 b1e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e59 b1e366
        have b1e375 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b1e371 X0
             have i₂ := b1e140
             grind)
          | exact superpose b1e140 b1e371
          | exact resolve b1e371 b1e140
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e140 b1e371
        have b1e1014 : y ≠ y := by
          first
          | (have i₁ := b1e164
             have i₂ := b1e375 (σ x)
             grind)
          | exact superpose b1e375 b1e164
          | (have r₁ := b1e164
             have r₂ := b1e375 (σ x)
             grind)
          | exact resolve b1e164 b1e375
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e164 b1e375
        have b1e1015 : False := by grind
        exact b1e1015
      · have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
        have b2e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
        have b2e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b2e183 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
        have b2e4277 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e69 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e4278 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e4277
             have r₂ := b2e22
             grind)
          | exact resolve b2e4277 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4277
        have b2e4279 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e4278
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e4278
          | exact resolve b2e4278 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4278
        have b2e4280 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e4279
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e4279
          | exact resolve b2e4279 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e4279
        have b2e8262 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
          intro X0
          grind
        clear b2e183
        have b2e8276 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b2e8262 X0
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e8262
          | exact resolve b2e8262 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8262
        have b2e9335 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e79 x x
             grind)
          | exact superpose b2e79 b2e21
          | (have j1 := b2e79 x x
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e79 x y
             grind)
          | exact resolve b2e21 b2e79
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e79
        have b2e9519 : (σ y) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e9335
        have b2e20247 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e9519
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e9519
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | exact resolve b2e9519 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e9519
        have b2e20257 : (σ y) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e20247
        have b2e20272 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e20257
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20257
          | exact resolve b2e20257 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20257
        have b2e20273 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
        clear b2e20272
        have b2e20285 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
          first
          | (have i₁ := b2e20273
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20273
          | exact resolve b2e20273 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20273
        have b2e20306 : x = (k x (τ (σ x))) ∨ x = y := by
          first
          | (have i₁ := b2e8276 x
             have i₂ := b2e20285
             grind)
          | exact superpose b2e20285 b2e8276
          | exact resolve b2e8276 b2e20285
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e8276 b2e20285
        have b2e20371 : x = (k x x) ∨ x = y := by
          first
          | (have i₁ := b2e20306
             have i₂ := b2e13 x
             grind)
          | exact superpose b2e13 b2e20306
          | exact resolve b2e20306 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20306
        have b2e20708 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = y := by
          first
          | (have i₁ := b2e17 x x
             have i₂ := b2e20371
             grind)
          | exact superpose b2e20371 b2e17
          | (have j0 := b2e17 x x
             grind)
          | exact resolve b2e17 b2e20371
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20371
        have b2e20721 : x = (M.op x x) ∨ x = y := by grind
        clear b2e20708
        have b2e20747 : x = y ∨ x = y := by
          first
          | (have i₁ := b2e20721
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e20721
          | exact resolve b2e20721 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e20721
        have b2e20748 : x = y := by grind
        clear b2e20747
        have b2e21066 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b2e4280
             have i₂ := b2e20748
             grind)
          | exact superpose b2e20748 b2e4280
          | exact resolve b2e4280 b2e20748
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e4280 b2e20748
        have b2e21078 : False := by grind
        exact b2e21078
  · rcases eq_or_ne (M.op y y) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
          intro X0 X1 X2
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
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
        have b3e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e38 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e12 y y x
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e12
          | exact resolve b3e12 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e47 : ∀ X0 : G, y = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b3e38 X0
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e38
          | exact resolve b3e38 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e38
        have b3e50 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op X0 y) := by
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
        have b3e51 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 y) := by
          intro X0 X1
          first
          | (have i₁ := b3e50 X0 X1
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e50
          | exact resolve b3e50 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e50
        have b3e52 : ∀ X0 : G, y = (M.op X0 y) := by
          intro X0
          first
          | (have i₁ := b3e51 X0 x
             have i₂ := b3e47 x
             grind)
          | exact superpose b3e47 b3e51
          | exact resolve b3e51 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e51
        have b3e56 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have i₁ := b3e16 X0 y
             have i₂ := b3e47 y
             grind)
          | exact superpose b3e47 b3e16
          | (have j0 := b3e16 X0 y
             grind)
          | (have r₁ := b3e16 X0 y
             have r₂ := b3e47 y
             grind)
          | exact resolve b3e16 b3e47
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e47
        have b3e57 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e56 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e63 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 y
             have i₂ := b3e52 (M.op X1 X1)
             grind)
          | exact superpose b3e52 b3e12
          | exact resolve b3e12 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e79 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X1)) = X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X2 X2) X0) = (M.op (M.op X2 X2) X0) := by
          intro X0 X1 X2
          first
          | (have i₁ := b3e12 X1 X2 (M.op X2 X2)
             have i₂ := b3e17 (M.op X2 X2) X0
             grind)
          | (have i₁ := b3e12 X0 X1 X2
             have i₂ := b3e17 X0 (M.op (M.op X1 X1) X2)
             grind)
          | exact superpose b3e17 b3e12
          | (have j1 := b3e17 X0 X0
             grind)
          | exact resolve b3e12 b3e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e96 : ∀ X0 X2 : G, (k (M.op X2 X2) X0) = (M.op (M.op X2 X2) X0) ∨ (M.op X0 X0) = X0 ∨ y = X0 := by
          intro X0 X2
          first
          | (have i₁ := b3e79 X0 x X2
             have i₂ := b3e63 x X2
             grind)
          | exact superpose b3e63 b3e79
          | (have j0 := b3e79 X0 x X2
             grind)
          | exact resolve b3e79 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e79
        have b3e106 : y = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e63 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e63
          | exact resolve b3e63 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e111 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = y := by
          intro X1 X2
          first
          | (have i₁ := b3e12 x X1 X2
             have i₂ := b3e63 x X1
             grind)
          | exact superpose b3e63 b3e12
          | exact resolve b3e12 b3e63
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e63
        have b3e161 : y ≠ (σ (M.op x y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e106
             grind)
          | exact superpose b3e106 b3e19
          | exact resolve b3e19 b3e106
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e106
        have b3e165 : y ≠ (σ y) := by
          first
          | (have i₁ := b3e161
             have i₂ := b3e52 x
             grind)
          | exact superpose b3e52 b3e161
          | exact resolve b3e161 b3e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52 b3e161
        have b3e187 : ∀ X0 : G, y = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b3e111 (σ x) X0
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e111
          | exact resolve b3e111 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e665 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
          intro X0
          grind
        clear b3e57
        have b3e680 : ∀ X0 : G, (k X0 y) = X0 := by
          intro X0
          first
          | (have j0 := b3e665 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e665
        have b3e911 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e27 X0 y
             have i₂ := b3e680 (τ X0)
             grind)
          | exact superpose b3e680 b3e27
          | exact resolve b3e27 b3e680
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e680
        have b3e912 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
          intro X0
          first
          | (have i₁ := b3e911 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e911
          | exact resolve b3e911 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e911
        have b3e4671 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e912 (M.op X0 X0)
             have i₂ := b3e96 (σ y) X0
             grind)
          | exact superpose b3e96 b3e912
          | (have j1 := b3e96 (σ y) x
             grind)
          | exact resolve b3e912 b3e96
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e96 b3e912
        have b3e4770 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have j0 := b3e4671 X0
             grind)
          | (have r₁ := b3e4671 X0
             have r₂ := b3e165
             grind)
          | exact resolve b3e4671 b3e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4671
        have b3e4852 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ y) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e4770 X0
             have i₂ := b3e111 X0 (σ y)
             grind)
          | exact superpose b3e111 b3e4770
          | exact resolve b3e4770 b3e111
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e111 b3e4770
        have b3e4885 : ∀ X0 : G, y = (σ y) ∨ (M.op X0 X0) = y := by
          intro X0
          first
          | (have i₁ := b3e4852 X0
             have i₂ := b3e187 (σ y)
             grind)
          | exact superpose b3e187 b3e4852
          | (have j0 := b3e4852 X0
             grind)
          | exact resolve b3e4852 b3e187
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e187 b3e4852
        have b3e4898 : ∀ X0 : G, (M.op X0 X0) = y := by
          intro X0
          first
          | (have j0 := b3e4885 X0
             grind)
          | (have r₁ := b3e4885 X0
             have r₂ := b3e165
             grind)
          | exact resolve b3e4885 b3e165
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e165 b3e4885
        have b3e4973 : y ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e4898 x
             grind)
          | exact superpose b3e4898 b3e20
          | (have r₁ := b3e20
             have r₂ := b3e4898 x
             grind)
          | exact resolve b3e20 b3e4898
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e4898
        have b3e4975 : False := by grind
        exact b3e4975
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op y y) := by grind
          have b4e24 : (σ y) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e39 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (σ y) X0) := by
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
          have b4e40 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b4e49 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b4e40 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e40
            | exact resolve b4e40 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40
          have b4e50 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
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
          have b4e53 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 y X1
               have i₂ := b4e49 X0
               grind)
            | exact superpose b4e49 b4e13
            | exact resolve b4e13 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e54 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b4e53 X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e53
            | exact resolve b4e53 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e55 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b4e54 X0 x
               have i₂ := b4e49 x
               grind)
            | exact superpose b4e49 b4e54
            | exact resolve b4e54 b4e49
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49 b4e54
          have b4e113 : y = (σ y) := by
            first
            | (have i₁ := b4e55 (σ y)
               have i₂ := b4e50 y
               grind)
            | exact superpose b4e50 b4e55
            | exact resolve b4e55 b4e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e50
          have b4e165 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e113
               grind)
            | exact superpose b4e113 b4e20
            | exact resolve b4e20 b4e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e170 : y ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e165
               have i₂ := b4e55 (σ x)
               grind)
            | exact superpose b4e55 b4e165
            | exact resolve b4e165 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e165
          have b4e171 : y ≠ (σ y) := by
            first
            | (have i₁ := b4e170
               have i₂ := b4e55 x
               grind)
            | exact superpose b4e55 b4e170
            | exact resolve b4e170 b4e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55 b4e170
          have b4e172 : False := by grind
          exact b4e172
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
            intro X0 X1 X2
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : y = (M.op y y) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e27 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e35 : ∀ X0 : G, (M.op y y) = (M.op y X0) := by
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
          have b5e45 : ∀ X0 : G, y = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b5e35 X0
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e48 : ∀ X0 X1 : G, (M.op (M.op y y) X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 y X1
               have i₂ := b5e45 X0
               grind)
            | exact superpose b5e45 b5e13
            | exact resolve b5e13 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e49 : ∀ X0 X1 : G, (M.op y X1) = (M.op X0 y) := by
            intro X0 X1
            first
            | (have i₁ := b5e48 X0 X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e48
            | exact resolve b5e48 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e50 : ∀ X0 : G, y = (M.op X0 y) := by
            intro X0
            first
            | (have i₁ := b5e49 X0 x
               have i₂ := b5e45 x
               grind)
            | exact superpose b5e45 b5e49
            | exact resolve b5e49 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e52 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b5e17 X0 y
               have i₂ := b5e45 y
               grind)
            | exact superpose b5e45 b5e17
            | (have j0 := b5e17 X0 y
               grind)
            | (have r₁ := b5e17 X0 y
               have r₂ := b5e45 y
               grind)
            | exact resolve b5e17 b5e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e45
          have b5e54 : ∀ X0 : G, (M.op X0 X0) = y ∨ (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e52 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = y := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 y
               have i₂ := b5e50 (M.op X1 X1)
               grind)
            | exact superpose b5e50 b5e13
            | exact resolve b5e13 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50
          have b5e82 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (σ y)
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ y) (σ y)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 X0 (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (k X0 (σ y)) = (M.op X0 (σ y)) := by
            intro X0
            first
            | (have j0 := b5e82 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e82
          have b5e106 : ∀ X1 X2 : G, (M.op (M.op X1 X1) X2) = y := by
            intro X1 X2
            first
            | (have i₁ := b5e13 x X1 X2
               have i₂ := b5e60 x X1
               grind)
            | exact superpose b5e60 b5e13
            | exact resolve b5e13 b5e60
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e60
          have b5e651 : ∀ X0 : G, (k X0 y) = X0 ∨ (k X0 y) = X0 := by
            intro X0
            grind
          clear b5e54
          have b5e670 : ∀ X0 : G, (k X0 y) = X0 := by
            intro X0
            first
            | (have j0 := b5e651 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e651
          have b5e766 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e27 X0 y
               have i₂ := b5e670 (τ X0)
               grind)
            | exact superpose b5e670 b5e27
            | exact resolve b5e27 b5e670
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e27 b5e670
          have b5e767 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e766 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e766
            | exact resolve b5e766 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e766
          have b5e1588 : ∀ X0 : G, y = (σ y) ∨ (k (M.op X0 X0) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
            intro X0
            first
            | (have i₁ := b5e106 X0 (M.op X0 X0)
               have i₂ := b5e87 (M.op X0 X0)
               grind)
            | exact superpose b5e87 b5e106
            | (have j1 := b5e87 (M.op X0 X0)
               grind)
            | exact resolve b5e106 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e87
          have b5e1599 : ∀ X0 : G, y = (k (M.op X0 X0) (σ y)) ∨ y = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1588 X0
               have i₂ := b5e106 X0 (σ y)
               grind)
            | exact superpose b5e106 b5e1588
            | exact resolve b5e1588 b5e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106 b5e1588
          have b5e1637 : ∀ X0 : G, (M.op X0 X0) = y ∨ y = (σ y) := by
            intro X0
            first
            | (have i₁ := b5e1599 X0
               have i₂ := b5e767 (M.op X0 X0)
               grind)
            | exact superpose b5e767 b5e1599
            | exact resolve b5e1599 b5e767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e767 b5e1599
          have b5e2301 : y ≠ y ∨ y = (σ y) := by
            first
            | (have i₁ := b5e21
               have i₂ := b5e1637 x
               grind)
            | exact superpose b5e1637 b5e21
            | (have r₁ := b5e21
               have r₂ := b5e1637 x
               grind)
            | exact resolve b5e21 b5e1637
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1637
          have b5e2303 : y = (σ y) := by grind
          clear b5e2301
          have b5e2431 : y ≠ (M.op y y) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e2303
               grind)
            | exact superpose b5e2303 b5e24
            | exact resolve b5e24 b5e2303
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e2303
          have b5e2443 : False := by grind
          exact b5e2443
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X1) X2) := by
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
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
        have b6e40 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e47 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e12 X2 X1 x
             grind)
          | (have i₁ := b6e12 X0 X1 (M.op X1 (M.op X1 X1))
             have i₂ := b6e12 (M.op X1 X1) X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e60 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X1
             have i₂ := b6e40 X0
             grind)
          | exact superpose b6e40 b6e40
          | exact resolve b6e40 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e40 X0
             grind)
          | exact superpose b6e40 b6e19
          | exact resolve b6e19 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
        have b6e92 : x = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
        have b6e93 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e25
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e25
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e25 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e25
        have b6e95 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e93
             have r₂ := b6e20
             grind)
          | exact resolve b6e93 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e93
        have b6e96 : x = (M.op x y) ∨ y = (M.op y y) := by
          first
          | (have r₁ := b6e92
             have r₂ := b6e20
             grind)
          | exact resolve b6e92 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e100 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e95
             have r₂ := b6e21
             grind)
          | exact resolve b6e95 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e101 : x = (M.op x y) := by
          first
          | (have r₁ := b6e96
             have r₂ := b6e21
             grind)
          | exact resolve b6e96 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e96
        have b6e289 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e47 X0 x y
             have i₂ := b6e101
             grind)
          | exact superpose b6e101 b6e47
          | exact resolve b6e47 b6e101
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e47 b6e101
        have b6e352 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e62 X0
             have i₂ := b6e100
             grind)
          | exact superpose b6e100 b6e62
          | exact resolve b6e62 b6e100
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e100
        have b6e497 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e352 x
             have i₂ := b6e40 x
             grind)
          | exact superpose b6e40 b6e352
          | exact resolve b6e352 b6e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40 b6e352
        have b6e1626 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y x) := by
          intro X0
          first
          | (have i₁ := b6e60 (M.op x (σ y)) X0
             have i₂ := b6e289 (σ y)
             grind)
          | exact superpose b6e289 b6e60
          | exact resolve b6e60 b6e289
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e60 b6e289
        have b6e6827 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e90 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e90
          | exact resolve b6e90 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e90
        have b6e7117 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e6827
        have b6e12246 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e7117
             grind)
          | exact superpose b6e7117 b6e13
          | exact resolve b6e13 b6e7117
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e12268 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e12246
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e12246
          | exact resolve b6e12246 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12246
        have b6e12284 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e12268
             grind)
          | exact superpose b6e12268 b6e17
          | (have j0 := b6e17 x x
             grind)
          | exact resolve b6e17 b6e12268
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12268
        have b6e12294 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e12284
        have b6e12304 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e12294
             have r₂ := b6e20
             grind)
          | exact resolve b6e12294 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e12294
        have b6e12581 : x = (k x x) ∨ (σ x) = (σ y) := by grind
        clear b6e12304
        have b6e13014 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e7117
             have i₂ := b6e12581
             grind)
          | exact superpose b6e12581 b6e7117
          | exact resolve b6e7117 b6e12581
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7117 b6e12581
        have b6e13029 : (σ x) = (σ y) := by grind
        clear b6e13014
        have b6e13546 : (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e22
             have i₂ := b6e13029
             grind)
          | exact superpose b6e13029 b6e22
          | exact resolve b6e22 b6e13029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e13556 : (σ y) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e497
             have i₂ := b6e13029
             grind)
          | exact superpose b6e13029 b6e497
          | exact resolve b6e497 b6e13029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e497
        have b6e13559 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
             have i₂ := b6e13029
             grind)
          | exact superpose b6e13029 b6e13
          | exact resolve b6e13 b6e13029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13029
        have b6e13579 : x = y := by
          first
          | (have i₁ := b6e13559
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e13559
          | exact resolve b6e13559 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13559
        have b6e13580 : (σ y) ≠ (M.op y x) := by
          first
          | (have i₁ := b6e13556
             have i₂ := b6e1626 (σ y)
             grind)
          | exact superpose b6e1626 b6e13556
          | exact resolve b6e13556 b6e1626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13556
        have b6e13583 : (σ y) = (M.op y x) := by
          first
          | (have i₁ := b6e13546
             have i₂ := b6e1626 (σ y)
             grind)
          | exact superpose b6e1626 b6e13546
          | exact resolve b6e13546 b6e1626
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1626 b6e13546
        have b6e13586 : (σ y) ≠ (M.op y y) := by
          first
          | (have i₁ := b6e13580
             have i₂ := b6e13579
             grind)
          | exact superpose b6e13579 b6e13580
          | exact resolve b6e13580 b6e13579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13580
        have b6e13587 : (σ y) = (M.op y y) := by
          first
          | (have i₁ := b6e13583
             have i₂ := b6e13579
             grind)
          | exact superpose b6e13579 b6e13583
          | exact resolve b6e13583 b6e13579
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e13579 b6e13583
        have b6e13590 : False := by grind
        exact b6e13590
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
          have b7e95 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
          have b7e98 : y = (M.op y y) := by grind
          clear b7e95
          have b7e102 : False := by grind
          exact b7e102
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
          have b8e62 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
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
          have b8e1834 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e62 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e62
          have b8e1835 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1834
               have r₂ := b8e24
               grind)
            | exact resolve b8e1834 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1834
          have b8e1836 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1835
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1835
            | exact resolve b8e1835 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1835
          have b8e1837 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1836
               grind)
            | exact superpose b8e1836 b8e20
            | exact resolve b8e20 b8e1836
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1836
          have b8e1855 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
            first
            | (have i₁ := b8e1837
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1837
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1837 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1837
          have b8e1856 : y = (M.op x x) ∨ y = (M.op y y) := by grind
          clear b8e1855
          have b8e1859 : y = (M.op y y) := by
            first
            | (have r₁ := b8e1856
               have r₂ := b8e21
               grind)
            | exact resolve b8e1856 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1856
          have b8e1862 : False := by grind
          exact b8e1862

/-- `Equation4449`: `x ◇ (y ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4449 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4449 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4449.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
        intro X0 X1 X2
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y x) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
      have b0e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
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
      have b0e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
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
      have b0e32 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
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
      have b0e34 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e35 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
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
      have b0e37 : (M.op x y) = (M.op y y) := by
        first
        | (have i₁ := b0e35 x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e40 : ∀ X1 : G, (M.op y y) = (M.op (M.op y X1) y) := by
        intro X1
        first
        | (have i₁ := b0e11 x y X1
           have i₂ := b0e35 x
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e42 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y X0) (M.op y y)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (M.op y X0) X0 X1
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e11
        | exact resolve b0e11 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e14 X1 (M.op X1 X2)
           have i₂ := b0e11 X0 X1 X2
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 X1 (M.op X1 X2)
           grind)
        | (have r₁ := b0e14 (M.op X1 (M.op (M.op X1 X2) X1)) (M.op (M.op X1 X2) X1)
           have r₂ := b0e11 (M.op (M.op X1 X2) X1) X1 X2
           grind)
        | (have r₁ := b0e14 X0 (M.op X0 (M.op X0 X0))
           have r₂ := b0e11 X0 X0 (M.op X0 X0)
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        grind
      have b0e75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e12 (k X0 (τ X1))
           have i₂ := b0e23 X1 X0
           grind)
        | exact superpose b0e23 b0e12
        | exact resolve b0e12 b0e23
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e164 : ∀ X0 X1 : G, (M.op y (M.op y y)) = (M.op X0 (M.op (M.op y X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X0 (M.op y X1) y
           have i₂ := b0e40 X1
           grind)
        | exact superpose b0e40 b0e36
        | exact resolve b0e36 b0e40
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40
      have b0e194 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op (M.op y X1) X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e164 X0 X1
           have i₂ := b0e35 y
           grind)
        | exact superpose b0e35 b0e164
        | exact resolve b0e164 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e164
      have b0e404 : ∀ X0 X1 X2 : G, (M.op (M.op y y) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X2) X1)) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e28 X1 X2 X0 (M.op y X0)
           have i₂ := b0e35 X0
           grind)
        | exact superpose b0e35 b0e28
        | exact resolve b0e28 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e422 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e28 X2 X4 (M.op X1 X2) X3
           have i₂ := b0e36 X2 X1 X0
           grind)
        | (have i₁ := b0e28 X2 X4 (M.op X1 X2) X3
           have i₂ := b0e36 X0 X1 X2
           grind)
        | exact superpose b0e36 b0e28
        | exact resolve b0e28 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X4) (M.op X1 X3)) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e11 X1 (M.op X1 X3) X4
           have i₂ := b0e28 X0 X2 X1 X3
           grind)
        | exact superpose b0e28 b0e11
        | exact resolve b0e11 b0e28
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e28
      have b0e501 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) = (M.op (M.op y (M.op X1 X3)) (M.op y y)) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e478 X0 X1 X2 X3 x
           have i₂ := b0e42 (M.op X1 X3) x
           grind)
        | exact superpose b0e42 b0e478
        | exact resolve b0e478 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e478
      have b0e527 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y (M.op X1 X2)) (M.op y y)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) := by
        intro X0 X1 X2 X4
        first
        | (have i₁ := b0e422 X0 X1 X2 x X4
           have i₂ := b0e42 (M.op X1 X2) x
           grind)
        | exact superpose b0e42 b0e422
        | exact resolve b0e422 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e422
      have b0e538 : ∀ X1 X3 : G, (M.op (M.op y (M.op X1 X3)) (M.op y y)) = (M.op X1 (M.op (M.op y y) X1)) := by
        intro X1 X3
        first
        | (have i₁ := b0e501 x X1 x X3
           have i₂ := b0e404 X1 x x
           grind)
        | exact superpose b0e404 b0e501
        | exact resolve b0e501 b0e404
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e404 b0e501
      have b0e551 : ∀ X1 X3 : G, (M.op y y) = (M.op (M.op y (M.op X1 X3)) (M.op y y)) := by
        intro X1 X3
        first
        | (have i₁ := b0e538 X1 X3
           have i₂ := b0e194 X1 y
           grind)
        | exact superpose b0e194 b0e538
        | exact resolve b0e538 b0e194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e194 b0e538
      have b0e644 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X4) X5) (M.op X1 X4)) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e29 (M.op (M.op X2 X3) X2) X1 X4 X5
           have i₂ := b0e32 X2 X3 X0 (M.op X1 (M.op (M.op X2 X3) X2))
           grind)
        | exact superpose b0e32 b0e29
        | exact resolve b0e29 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e675 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X3)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) = (M.op (M.op (M.op X4 X5) X4) X0) := by
        intro X0 X1 X2 X3 X4 X5
        first
        | (have i₁ := b0e32 X4 X5 (M.op X3 (M.op X0 X3)) X0
           have i₂ := b0e29 X3 X0 X1 X2
           grind)
        | exact superpose b0e29 b0e32
        | exact resolve b0e32 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e677 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op X4 (M.op X0 X4)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e36 X3 X0 (M.op X4 (M.op X0 X4))
           have i₂ := b0e29 X4 X0 X1 X2
           grind)
        | exact superpose b0e29 b0e36
        | exact resolve b0e36 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e680 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op X2 (M.op (σ y) X2)) (M.op (M.op (M.op (σ y) X0) X1) (M.op (σ y) X0))) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e34 (M.op X2 (M.op (σ y) X2))
           have i₂ := b0e29 X2 (σ y) X0 X1
           grind)
        | exact superpose b0e29 b0e34
        | exact resolve b0e34 b0e29
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29 b0e34
      have b0e686 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op y (M.op (σ y) (M.op (σ y) X0))) (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e680 X0 x x
           have i₂ := b0e527 x (σ y) (M.op (σ y) X0) x
           grind)
        | exact superpose b0e527 b0e680
        | exact resolve b0e680 b0e527
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e680
      have b0e689 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op y (M.op X0 (M.op X0 X1))) (M.op y y)) := by
        intro X0 X1 X3
        first
        | (have i₁ := b0e677 X0 X1 x X3 x
           have i₂ := b0e527 x X0 (M.op X0 X1) x
           grind)
        | exact superpose b0e527 b0e677
        | exact resolve b0e677 b0e527
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e677
      have b0e691 : ∀ X0 X1 X4 X5 : G, (M.op (M.op (M.op X4 X5) X4) X0) = (M.op (M.op y (M.op X0 (M.op X0 X1))) (M.op y y)) := by
        intro X0 X1 X4 X5
        first
        | (have i₁ := b0e675 X0 X1 x x X4 X5
           have i₂ := b0e527 x X0 (M.op X0 X1) x
           grind)
        | exact superpose b0e527 b0e675
        | exact resolve b0e675 b0e527
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e527 b0e675
      have b0e703 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y (M.op X1 X4)) (M.op y y)) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
        intro X0 X1 X2 X3 X4
        first
        | (have i₁ := b0e644 X0 X1 X2 X3 X4 x
           have i₂ := b0e42 (M.op X1 X4) x
           grind)
        | exact superpose b0e42 b0e644
        | exact resolve b0e644 b0e42
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e42 b0e644
      have b0e756 : (M.op (σ y) (σ y)) = (M.op y y) := by
        first
        | (have i₁ := b0e686 x
           have i₂ := b0e551 (σ y) (M.op (σ y) x)
           grind)
        | exact superpose b0e551 b0e686
        | exact resolve b0e686 b0e551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e686
      have b0e758 : ∀ X0 X3 : G, (M.op X3 (M.op X0 X3)) = (M.op y y) := by
        intro X0 X3
        first
        | (have i₁ := b0e689 X0 x X3
           have i₂ := b0e551 X0 (M.op X0 x)
           grind)
        | exact superpose b0e551 b0e689
        | exact resolve b0e689 b0e551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e689
      have b0e760 : ∀ X0 X4 X5 : G, (M.op y y) = (M.op (M.op (M.op X4 X5) X4) X0) := by
        intro X0 X4 X5
        first
        | (have i₁ := b0e691 X0 x X4 X5
           have i₂ := b0e551 X0 (M.op X0 x)
           grind)
        | exact superpose b0e551 b0e691
        | exact resolve b0e691 b0e551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e691
      have b0e770 : ∀ X0 X1 X2 X3 : G, (M.op y y) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
        intro X0 X1 X2 X3
        first
        | (have i₁ := b0e703 X0 X1 X2 X3 x
           have i₂ := b0e551 X1 x
           grind)
        | exact superpose b0e551 b0e703
        | exact resolve b0e703 b0e551
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e551 b0e703
      have b0e812 : ∀ X1 : G, (M.op y y) = (M.op X1 (M.op y y)) := by
        intro X1
        first
        | (have i₁ := b0e770 x X1 x x
           have i₂ := b0e758 (M.op X1 (M.op (M.op x x) x)) x
           grind)
        | exact superpose b0e758 b0e770
        | exact resolve b0e770 b0e758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e770
      have b0e855 : (σ y) ≠ (M.op y y) ∨ (M.op y y) = (k (σ y) (σ y)) := by
        first
        | (have i₁ := b0e14 (σ y) (σ y)
           have i₂ := b0e756
           grind)
        | exact superpose b0e756 b0e14
        | exact resolve b0e14 b0e756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e868 : (M.op y y) = (σ (k y y)) ∨ (σ y) ≠ (M.op y y) := by
        first
        | (have i₁ := b0e855
           have i₂ := b0e17 y y
           grind)
        | exact superpose b0e17 b0e855
        | exact resolve b0e855 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e855
      have b0e1204 : (M.op (σ x) (σ y)) = (M.op y y) := by
        first
        | (have i₁ := b0e758 (σ y) (σ x)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e758
        | exact resolve b0e758 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1340 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
        intro X0
        first
        | (have j0 := b0e45 X0 X0 (M.op X0 X0)
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e1341 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op y y)) := by
        intro X0
        first
        | (have i₁ := b0e1340 X0
           have i₂ := b0e758 X0 X0
           grind)
        | exact superpose b0e758 b0e1340
        | exact resolve b0e1340 b0e758
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e758 b0e1340
      have b0e1533 : (M.op y y) = (σ (k y y)) ∨ (σ y) = (M.op y y) := by
        first
        | (have i₁ := b0e53 y
           have i₂ := b0e756
           grind)
        | exact superpose b0e756 b0e53
        | exact resolve b0e53 b0e756
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53 b0e756
      have b0e1578 : (M.op y y) = (σ (k y y)) := by
        first
        | (have r₁ := b0e1533
           have r₂ := b0e868
           grind)
        | exact resolve b0e1533 b0e868
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e868 b0e1533
      have b0e1605 : (k y y) = (τ (M.op y y)) := by
        first
        | (have i₁ := b0e12 (k y y)
           have i₂ := b0e1578
           grind)
        | exact superpose b0e1578 b0e12
        | exact resolve b0e12 b0e1578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e1995 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b0e75 X0 (M.op y y)
           have i₂ := b0e1341 (σ X0)
           grind)
        | exact superpose b0e1341 b0e75
        | exact resolve b0e75 b0e1341
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e75 b0e1341
      have b0e1997 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (k y y)) := by
        intro X0
        first
        | (have i₁ := b0e1995 X0
           have i₂ := b0e1605
           grind)
        | exact superpose b0e1605 b0e1995
        | exact resolve b0e1995 b0e1605
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1995
      have b0e2096 : (σ (M.op x y)) ≠ (M.op y y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e1204
           grind)
        | exact superpose b0e1204 b0e18
        | exact resolve b0e18 b0e1204
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1204
      have b0e2126 : (M.op y y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e2096
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e2096
        | exact resolve b0e2096 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e2096
      have b0e8580 : (k (k y y) (k y y)) = (τ (M.op (M.op y y) (M.op y y))) := by
        first
        | (have i₁ := b0e1997 (k y y)
           have i₂ := b0e1578
           grind)
        | exact superpose b0e1578 b0e1997
        | exact resolve b0e1997 b0e1578
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1997
      have b0e8594 : (k (k y y) (k y y)) = (τ (M.op y y)) := by
        first
        | (have i₁ := b0e8580
           have i₂ := b0e812 (M.op y y)
           grind)
        | exact superpose b0e812 b0e8580
        | exact resolve b0e8580 b0e812
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e812 b0e8580
      have b0e8598 : (k y y) = (k (k y y) (k y y)) := by
        first
        | (have i₁ := b0e8594
           have i₂ := b0e1605
           grind)
        | exact superpose b0e1605 b0e8594
        | exact resolve b0e8594 b0e1605
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1605 b0e8594
      have b0e9556 : (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) := by grind
      clear b0e8598
      have b0e9557 : (k y y) = (M.op (k y y) (k y y)) := by grind
      clear b0e9556
      have b0e9911 : ∀ X0 : G, (M.op y y) = (M.op (M.op (k y y) (k y y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e760 X0 (k y y) (k y y)
           have i₂ := b0e9557
           grind)
        | exact superpose b0e9557 b0e760
        | exact resolve b0e760 b0e9557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e760
      have b0e9917 : ∀ X0 : G, (M.op y y) = (M.op (k y y) X0) := by
        intro X0
        first
        | (have i₁ := b0e9911 X0
           have i₂ := b0e9557
           grind)
        | exact superpose b0e9557 b0e9911
        | exact resolve b0e9911 b0e9557
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9911
      have b0e10459 : (M.op y y) = (k y y) := by
        first
        | (have i₁ := b0e9557
           have i₂ := b0e9917 (k y y)
           grind)
        | exact superpose b0e9917 b0e9557
        | exact resolve b0e9557 b0e9917
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e9557 b0e9917
      have b0e11007 : (M.op y y) = (σ (M.op y y)) := by
        first
        | (have i₁ := b0e1578
           have i₂ := b0e10459
           grind)
        | exact superpose b0e10459 b0e1578
        | exact resolve b0e1578 b0e10459
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1578 b0e10459
      have b0e11015 : False := by grind
      exact b0e11015
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (σ y) := by grind
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
        have b1e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b1e13 x
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e13
          | exact resolve b1e13 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e27 : x = y := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e13 y
             grind)
          | exact superpose b1e13 b1e26
          | exact resolve b1e26 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e28 : y = (M.op y y) := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e20
          | exact resolve b1e20 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e54 : y ≠ y ∨ y = (k y y) := by
          first
          | (have i₁ := b1e15 y y
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e15
          | (have r₁ := b1e15 y y
             have r₂ := b1e28
             grind)
          | exact resolve b1e15 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28
        have b1e58 : y = (k y y) := by grind
        clear b1e54
        have b1e65 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b1e2384 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e65 y
             grind)
          | exact superpose b1e65 b1e24
          | (have j1 := b1e65 y
             grind)
          | (have r₁ := b1e24
             have r₂ := b1e65 y
             grind)
          | exact resolve b1e24 b1e65
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e65
        have b1e2429 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e2384
             have r₂ := b1e24
             grind)
          | exact resolve b1e2384 b1e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e2384
        have b1e2452 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e2429
             have i₂ := b1e58
             grind)
          | exact superpose b1e58 b1e2429
          | exact resolve b1e2429 b1e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e58 b1e2429
        have b1e2453 : False := by grind
        exact b1e2453
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b2e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b2e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b2e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b2e25 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
        have b2e26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
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
        have b2e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X1 (M.op X1 X2) X3
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e28 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e12 x X0 X3
             have i₂ := b2e12 x X0 X1
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e29 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op y y) := by
          intro X0
          first
          | (have i₁ := b2e12 X0 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
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
        have b2e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X1 X3) X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e12 X2 (M.op X1 X3) X1
             have i₂ := b2e12 X0 X1 X3
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
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
        have b2e33 : (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b2e29 x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e29
          | exact resolve b2e29 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e36 : ∀ X1 : G, (M.op y y) = (M.op (M.op y X1) y) := by
          intro X1
          first
          | (have i₁ := b2e12 x y X1
             have i₂ := b2e29 x
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e38 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op y X0) (M.op y y)) := by
          intro X0 X1
          first
          | (have i₁ := b2e12 (M.op y X0) X0 X1
             have i₂ := b2e29 X0
             grind)
          | exact superpose b2e29 b2e12
          | exact resolve b2e12 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e39 : y ≠ y ∨ (k x y) = (M.op x x) := by
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
        have b2e42 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e15 X1 (M.op X1 X2)
             have i₂ := b2e12 X0 X1 X2
             grind)
          | exact superpose b2e12 b2e15
          | (have j0 := b2e15 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b2e15 (M.op X1 (M.op (M.op X1 X2) X1)) (M.op (M.op X1 X2) X1)
             have r₂ := b2e12 (M.op (M.op X1 X2) X1) X1 X2
             grind)
          | (have r₁ := b2e15 X0 (M.op X0 (M.op X0 X0))
             have r₂ := b2e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b2e15 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e43 : (k x y) = (M.op x x) := by grind
        clear b2e39
        have b2e45 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
        have b2e62 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k (τ X0) X1)
             have i₂ := b2e24 X0 X1
             grind)
          | exact superpose b2e24 b2e13
          | exact resolve b2e13 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
          intro X0 X1
          first
          | (have i₁ := b2e13 (k X0 (τ X1))
             have i₂ := b2e25 X1 X0
             grind)
          | exact superpose b2e25 b2e13
          | exact resolve b2e13 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e116 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e62 X1 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e62
          | exact resolve b2e62 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e148 : ∀ X0 X1 : G, (M.op y (M.op y y)) = (M.op X0 (M.op (M.op y X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e32 X0 (M.op y X1) y
             have i₂ := b2e36 X1
             grind)
          | exact superpose b2e36 b2e32
          | exact resolve b2e32 b2e36
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36
        have b2e149 : ∀ X0 : G, (M.op y (M.op y y)) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e32 X0 x y
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e32
          | exact resolve b2e32 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e174 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x X0)) := by
          intro X0
          first
          | (have i₁ := b2e149 X0
             have i₂ := b2e29 y
             grind)
          | exact superpose b2e29 b2e149
          | exact resolve b2e149 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e149
        have b2e175 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 (M.op (M.op y X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e148 X0 X1
             have i₂ := b2e29 y
             grind)
          | exact superpose b2e29 b2e148
          | exact resolve b2e148 b2e29
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e29 b2e148
        have b2e289 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op X3 X2) (M.op (M.op X3 X4) X3)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e26 X3 X4 X2 (M.op X1 X2)
             have i₂ := b2e32 X2 X1 X0
             grind)
          | (have i₁ := b2e26 X3 X4 X2 (M.op X1 X2)
             have i₂ := b2e32 X0 X1 X2
             grind)
          | exact superpose b2e32 b2e26
          | exact resolve b2e26 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e292 : ∀ X0 X1 X2 : G, (M.op (M.op y y) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e26 X1 X2 X0 (M.op x X0)
             have i₂ := b2e174 X0
             grind)
          | exact superpose b2e174 b2e26
          | exact resolve b2e26 b2e174
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e174
        have b2e308 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e26 X2 X4 (M.op X1 X2) X3
             have i₂ := b2e32 X2 X1 X0
             grind)
          | (have i₁ := b2e26 X2 X4 (M.op X1 X2) X3
             have i₂ := b2e32 X0 X1 X2
             grind)
          | exact superpose b2e32 b2e26
          | exact resolve b2e26 b2e32
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e352 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X4) (M.op X1 X3)) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 X1 (M.op X1 X3) X4
             have i₂ := b2e26 X0 X2 X1 X3
             grind)
          | exact superpose b2e26 b2e12
          | exact resolve b2e12 b2e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e26
        have b2e375 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) = (M.op (M.op y (M.op X1 X3)) (M.op y y)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e352 X0 X1 X2 X3 x
             have i₂ := b2e38 (M.op X1 X3) x
             grind)
          | exact superpose b2e38 b2e352
          | exact resolve b2e352 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e352
        have b2e391 : ∀ X0 X1 X2 X4 : G, (M.op (M.op y (M.op X1 X2)) (M.op y y)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b2e308 X0 X1 X2 x X4
             have i₂ := b2e38 (M.op X1 X2) x
             grind)
          | exact superpose b2e38 b2e308
          | exact resolve b2e308 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e308
        have b2e394 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X0)) X2) = (M.op (M.op y y) X2) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e289 X0 X1 X2 x x
             have i₂ := b2e292 X2 x x
             grind)
          | exact superpose b2e292 b2e289
          | exact resolve b2e289 b2e292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e289
        have b2e399 : ∀ X1 X3 : G, (M.op (M.op y (M.op X1 X3)) (M.op y y)) = (M.op X1 (M.op (M.op y y) X1)) := by
          intro X1 X3
          first
          | (have i₁ := b2e375 x X1 x X3
             have i₂ := b2e292 X1 x x
             grind)
          | exact superpose b2e292 b2e375
          | exact resolve b2e375 b2e292
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e292 b2e375
        have b2e407 : ∀ X1 X3 : G, (M.op y y) = (M.op (M.op y (M.op X1 X3)) (M.op y y)) := by
          intro X1 X3
          first
          | (have i₁ := b2e399 X1 X3
             have i₂ := b2e175 X1 y
             grind)
          | exact superpose b2e175 b2e399
          | exact resolve b2e399 b2e175
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175 b2e399
        have b2e472 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X1 X4) X5) (M.op X1 X4)) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
          intro X0 X1 X2 X3 X4 X5
          first
          | (have i₁ := b2e27 (M.op (M.op X2 X3) X2) X1 X4 X5
             have i₂ := b2e30 X2 X3 X0 (M.op X1 (M.op (M.op X2 X3) X2))
             grind)
          | exact superpose b2e30 b2e27
          | exact resolve b2e27 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e494 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X4) X0) = (M.op (M.op X3 (M.op X0 X3)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e12 (M.op X3 (M.op X0 X3)) X0 X4
             have i₂ := b2e27 X3 X0 X1 X2
             grind)
          | exact superpose b2e27 b2e12
          | exact resolve b2e12 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e505 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op X4 (M.op X0 X4)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e32 X3 X0 (M.op X4 (M.op X0 X4))
             have i₂ := b2e27 X4 X0 X1 X2
             grind)
          | exact superpose b2e27 b2e32
          | exact resolve b2e32 b2e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27 b2e32
        have b2e513 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op y (M.op X0 (M.op X0 X1))) (M.op y y)) := by
          intro X0 X1 X3
          first
          | (have i₁ := b2e505 X0 X1 x X3 x
             have i₂ := b2e391 x X0 (M.op X0 X1) x
             grind)
          | exact superpose b2e391 b2e505
          | exact resolve b2e505 b2e391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e505
        have b2e518 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X4) X0) = (M.op (M.op y (M.op X0 (M.op X0 X1))) (M.op y y)) := by
          intro X0 X1 X4
          first
          | (have i₁ := b2e494 X0 X1 x x X4
             have i₂ := b2e391 x X0 (M.op X0 X1) x
             grind)
          | exact superpose b2e391 b2e494
          | exact resolve b2e494 b2e391
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e391 b2e494
        have b2e527 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op y (M.op X1 X4)) (M.op y y)) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e472 X0 X1 X2 X3 X4 x
             have i₂ := b2e38 (M.op X1 X4) x
             grind)
          | exact superpose b2e38 b2e472
          | exact resolve b2e472 b2e38
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e38 b2e472
        have b2e571 : ∀ X0 X3 : G, (M.op y y) = (M.op X3 (M.op X0 X3)) := by
          intro X0 X3
          first
          | (have i₁ := b2e513 X0 x X3
             have i₂ := b2e407 X0 (M.op X0 x)
             grind)
          | exact superpose b2e407 b2e513
          | exact resolve b2e513 b2e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e513
        have b2e576 : ∀ X0 X4 : G, (M.op y y) = (M.op (M.op X0 X4) X0) := by
          intro X0 X4
          first
          | (have i₁ := b2e518 X0 x X4
             have i₂ := b2e407 X0 (M.op X0 x)
             grind)
          | exact superpose b2e407 b2e518
          | exact resolve b2e518 b2e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e518
        have b2e583 : ∀ X0 X1 X2 X3 : G, (M.op y y) = (M.op X1 (M.op X0 (M.op (M.op X1 (M.op (M.op X2 X3) X2)) X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b2e527 X0 X1 X2 X3 x
             have i₂ := b2e407 X1 x
             grind)
          | exact superpose b2e407 b2e527
          | exact resolve b2e527 b2e407
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e407 b2e527
        have b2e619 : ∀ X1 : G, (M.op y y) = (M.op X1 (M.op y y)) := by
          intro X1
          first
          | (have i₁ := b2e583 x X1 x x
             have i₂ := b2e571 (M.op X1 (M.op (M.op x x) x)) x
             grind)
          | exact superpose b2e571 b2e583
          | exact resolve b2e583 b2e571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e583
        have b2e820 : ∀ X0 X1 X2 : G, (M.op y y) = (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b2e571 (M.op X1 X2) x
             have i₂ := b2e31 X0 X1 x X2
             grind)
          | exact superpose b2e31 b2e571
          | exact resolve b2e571 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e830 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op X0 (M.op X1 X0)) (M.op X1 X2)) X3) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b2e28 X3 X4 (M.op (M.op X1 X2) X3)
             have i₂ := b2e31 X0 X1 X3 X2
             grind)
          | exact superpose b2e31 b2e28
          | exact resolve b2e28 b2e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28 b2e31
        have b2e895 : ∀ X1 X2 X3 X4 : G, (M.op (M.op X3 X4) X3) = (M.op (M.op (M.op y y) (M.op X1 X2)) X3) := by
          intro X1 X2 X3 X4
          first
          | (have i₁ := b2e830 x X1 X2 X3 X4
             have i₂ := b2e394 x X1 (M.op X1 X2)
             grind)
          | exact superpose b2e394 b2e830
          | exact resolve b2e830 b2e394
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e830
        have b2e903 : ∀ X1 X2 : G, (M.op y y) = (M.op (M.op y y) (M.op X1 X2)) := by
          intro X1 X2
          first
          | (have i₁ := b2e820 x X1 X2
             have i₂ := b2e394 x X1 (M.op X1 X2)
             grind)
          | exact superpose b2e394 b2e820
          | exact resolve b2e820 b2e394
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e394 b2e820
        have b2e959 : ∀ X1 X2 X3 : G, (M.op y y) = (M.op (M.op (M.op y y) (M.op X1 X2)) X3) := by
          intro X1 X2 X3
          first
          | (have i₁ := b2e895 X1 X2 X3 x
             have i₂ := b2e576 X3 x
             grind)
          | exact superpose b2e576 b2e895
          | exact resolve b2e895 b2e576
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e576 b2e895
        have b2e996 : ∀ X3 : G, (M.op y y) = (M.op (M.op y y) X3) := by
          intro X3
          first
          | (have i₁ := b2e959 x x X3
             have i₂ := b2e903 x x
             grind)
          | exact superpose b2e903 b2e959
          | exact resolve b2e959 b2e903
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e903 b2e959
        have b2e1145 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b2e42 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e42
        have b2e1146 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b2e1145 X0
             have i₂ := b2e571 X0 X0
             grind)
          | exact superpose b2e571 b2e1145
          | exact resolve b2e1145 b2e571
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1145
        have b2e1310 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have j0 := b2e45 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1494 : ∀ X0 : G, (M.op y y) = (M.op X0 (k X0 (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e571 X0 X0
             have i₂ := b2e1146 X0
             grind)
          | exact superpose b2e1146 b2e571
          | exact resolve b2e571 b2e1146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1502 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e24 X0 (M.op y y)
             have i₂ := b2e1146 (τ X0)
             grind)
          | exact superpose b2e1146 b2e24
          | exact resolve b2e24 b2e1146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24
        have b2e1553 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e50 x y
             grind)
          | exact superpose b2e50 b2e19
          | (have j1 := b2e50 x y
             grind)
          | exact resolve b2e19 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1578 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e15 (σ X1) (σ X0)
             have i₂ := b2e50 X1 X0
             grind)
          | exact superpose b2e50 b2e15
          | (have j0 := b2e15 (σ X1) (σ X0)
             have j1 := b2e50 X1 X0
             grind)
          | (have r₁ := b2e15 (σ X0) (σ X1)
             have r₂ := b2e50 X0 X1
             grind)
          | exact resolve b2e15 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50
        have b2e1598 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have j0 := b2e1578 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1578
        have b2e1615 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
          intro X0 X1
          first
          | (have i₁ := b2e1598 X0 X1
             have i₂ := b2e18 X1 X0
             grind)
          | exact superpose b2e18 b2e1598
          | (have j0 := b2e1598 X0 X1
             grind)
          | exact resolve b2e1598 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1598
        have b2e1636 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b2e1553
             have r₂ := b2e21
             grind)
          | exact resolve b2e1553 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1553
        have b2e1658 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e1636
             have r₂ := b2e22
             grind)
          | exact resolve b2e1636 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1636
        have b2e1661 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1658
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e1658
          | exact resolve b2e1658 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43 b2e1658
        have b2e1662 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b2e1661
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e1661
          | exact resolve b2e1661 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1661
        have b2e1669 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e71 X0 (M.op y y)
             have i₂ := b2e1146 (σ X0)
             grind)
          | exact superpose b2e1146 b2e71
          | exact resolve b2e71 b2e1146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e7154 : ∀ X0 : G, (k (σ X0) (σ (M.op y y))) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1502 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e1502
          | exact resolve b2e1502 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e7184 : ∀ X0 : G, (σ (M.op X0 X0)) = (σ (k X0 (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e7154 X0
             have i₂ := b2e18 X0 (M.op y y)
             grind)
          | exact superpose b2e18 b2e7154
          | exact resolve b2e7154 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7154
        have b2e7328 : ∀ X0 : G, (k (τ X0) (τ (M.op y y))) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1669 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e1669
          | exact resolve b2e1669 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1669
        have b2e7350 : ∀ X0 : G, (τ (M.op X0 X0)) = (τ (k X0 (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b2e7328 X0
             have i₂ := b2e116 (M.op y y) X0
             grind)
          | exact superpose b2e116 b2e7328
          | exact resolve b2e7328 b2e116
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e116 b2e7328
        have b2e28492 : (σ (M.op y y)) ≠ (σ (M.op (M.op y y) (M.op y y))) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e1310 (M.op y y)
             have i₂ := b2e7184 (M.op y y)
             grind)
          | exact superpose b2e7184 b2e1310
          | (have j0 := b2e1310 (M.op y y)
             grind)
          | exact resolve b2e1310 b2e7184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1310 b2e7184
        have b2e28493 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e28492
             have i₂ := b2e619 (M.op y y)
             grind)
          | exact superpose b2e619 b2e28492
          | exact resolve b2e28492 b2e619
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28492
        have b2e28494 : (σ (M.op y y)) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by grind
        clear b2e28493
        have b2e28502 : (σ (M.op y y)) = (k (σ (M.op y y)) (M.op y y)) := by
          first
          | (have i₁ := b2e28494
             have i₂ := b2e1146 (σ (M.op y y))
             grind)
          | exact superpose b2e1146 b2e28494
          | exact resolve b2e28494 b2e1146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28494
        have b2e32189 : (τ (σ (M.op y y))) = (k (M.op y y) (τ (M.op y y))) := by
          first
          | (have i₁ := b2e71 (M.op y y) (M.op y y)
             have i₂ := b2e28502
             grind)
          | exact superpose b2e28502 b2e71
          | exact resolve b2e71 b2e28502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e32191 : (M.op y y) = (M.op (σ (M.op y y)) (σ (M.op y y))) := by
          first
          | (have i₁ := b2e1494 (σ (M.op y y))
             have i₂ := b2e28502
             grind)
          | exact superpose b2e28502 b2e1494
          | exact resolve b2e1494 b2e28502
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1494
        have b2e32193 : (M.op y y) = (k (σ (M.op y y)) (M.op y y)) := by
          first
          | (have i₁ := b2e32191
             have i₂ := b2e1146 (σ (M.op y y))
             grind)
          | exact superpose b2e1146 b2e32191
          | exact resolve b2e32191 b2e1146
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32191
        have b2e32195 : (M.op y y) = (k (M.op y y) (τ (M.op y y))) := by
          first
          | (have i₁ := b2e32189
             have i₂ := b2e13 (M.op y y)
             grind)
          | exact superpose b2e13 b2e32189
          | exact resolve b2e32189 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32189
        have b2e34328 : (M.op y y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e28502
             have i₂ := b2e32193
             grind)
          | exact superpose b2e32193 b2e28502
          | exact resolve b2e28502 b2e32193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28502
        have b2e34331 : (τ (M.op y y)) = (k (M.op y y) (τ (M.op y y))) := by
          first
          | (have i₁ := b2e71 (M.op y y) (M.op y y)
             have i₂ := b2e32193
             grind)
          | exact superpose b2e32193 b2e71
          | exact resolve b2e71 b2e32193
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71 b2e32193
        have b2e34335 : (M.op y y) = (τ (M.op y y)) := by
          first
          | (have i₁ := b2e34331
             have i₂ := b2e32195
             grind)
          | exact superpose b2e32195 b2e34331
          | exact resolve b2e34331 b2e32195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e32195 b2e34331
        have b2e36344 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (M.op y y)) := by
          intro X0
          first
          | (have i₁ := b2e1502 X0
             have i₂ := b2e34328
             grind)
          | exact superpose b2e34328 b2e1502
          | exact resolve b2e1502 b2e34328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1502
        have b2e43424 : ∀ X0 : G, (k (σ X0) (M.op y y)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e36344 (σ X0)
             have i₂ := b2e13 X0
             grind)
          | exact superpose b2e13 b2e36344
          | exact resolve b2e36344 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e36344
        have b2e45957 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e1146 (σ X0)
             have i₂ := b2e43424 X0
             grind)
          | exact superpose b2e43424 b2e1146
          | exact resolve b2e1146 b2e43424
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1146 b2e43424
        have b2e48949 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e45 X0
             have i₂ := b2e45957 X0
             grind)
          | exact superpose b2e45957 b2e45
          | exact resolve b2e45 b2e45957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45
        have b2e48956 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e15 (σ X0) (σ X0)
             have i₂ := b2e45957 X0
             grind)
          | exact superpose b2e45957 b2e15
          | exact resolve b2e15 b2e45957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e49143 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b2e48956 X0
             have i₂ := b2e18 X0 X0
             grind)
          | exact superpose b2e18 b2e48956
          | (have j0 := b2e48956 X0
             grind)
          | exact resolve b2e48956 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48956
        have b2e49208 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b2e49143 X0
             have j1 := b2e48949 X0
             grind)
          | (have r₁ := b2e49143 X0
             have r₂ := b2e48949 X0
             grind)
          | exact resolve b2e49143 b2e48949
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48949 b2e49143
        have b2e51795 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
          intro X0
          first
          | (have i₁ := b2e13 (k X0 X0)
             have i₂ := b2e49208 X0
             grind)
          | exact superpose b2e49208 b2e13
          | exact resolve b2e13 b2e49208
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e49208
        have b2e51832 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have i₁ := b2e51795 X0
             have i₂ := b2e13 (M.op X0 X0)
             grind)
          | exact superpose b2e13 b2e51795
          | exact resolve b2e51795 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51795
        have b2e281501 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1615 x y
             grind)
          | exact superpose b2e1615 b2e21
          | (have j1 := b2e1615 x y
             grind)
          | exact resolve b2e21 b2e1615
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1615
        have b2e281971 : (σ y) ≠ (σ (k y x)) ∨ (σ (k y x)) = (M.op (σ y) (σ y)) := by
          first
          | (have r₁ := b2e281501
             have r₂ := b2e22
             grind)
          | exact resolve b2e281501 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e281501
        have b2e282580 : (σ (M.op y y)) = (σ (k y x)) ∨ (σ y) ≠ (σ (k y x)) := by
          first
          | (have i₁ := b2e281971
             have i₂ := b2e45957 y
             grind)
          | exact superpose b2e45957 b2e281971
          | exact resolve b2e281971 b2e45957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e281971
        have b2e282928 : (σ y) ≠ (σ (k y x)) ∨ (M.op y y) = (σ (k y x)) := by
          first
          | (have i₁ := b2e282580
             have i₂ := b2e34328
             grind)
          | exact superpose b2e34328 b2e282580
          | exact resolve b2e282580 b2e34328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e282580
        have b2e283179 : (σ y) ≠ (σ (M.op y x)) ∨ (M.op y y) = (σ (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e282928
             have i₂ := b2e17 y x
             grind)
          | exact superpose b2e17 b2e282928
          | (have j1 := b2e17 (M.op y y) (σ (M.op y x))
             grind)
          | (have r₁ := b2e282928
             have r₂ := b2e17 (σ y) (σ (k y x))
             grind)
          | (have r₁ := b2e282928
             have r₂ := b2e17 (σ (k y x)) (σ y)
             grind)
          | exact resolve b2e282928 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e282928
        have b2e283180 : (σ y) ≠ (σ y) ∨ (M.op y y) = (σ (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e283179
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e283179
          | exact resolve b2e283179 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e283179
        have b2e283181 : (M.op y y) = (σ (M.op y x)) ∨ x = y ∨ x = (M.op x y) := by grind
        clear b2e283180
        have b2e283182 : (σ y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
          first
          | (have i₁ := b2e283181
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e283181
          | exact resolve b2e283181 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e283181
        have b2e283183 : (σ y) = (M.op y y) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e283182
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e283182
          | exact resolve b2e283182 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e283182
        have b2e285620 : (σ y) = (τ (σ y)) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e34335
             have i₂ := b2e283183
             grind)
          | exact superpose b2e283183 b2e34335
          | exact resolve b2e34335 b2e283183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e285661 : (τ (σ y)) = (τ (k y (σ y))) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e7350 y
             have i₂ := b2e283183
             grind)
          | exact superpose b2e283183 b2e7350
          | exact resolve b2e7350 b2e283183
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e7350 b2e283183
        have b2e286033 : (τ (σ y)) = (k (τ y) y) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e285661
             have i₂ := b2e62 y y
             grind)
          | exact superpose b2e62 b2e285661
          | exact resolve b2e285661 b2e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285661
        have b2e286051 : x = (M.op y y) ∨ y = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e285620
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e285620
          | exact resolve b2e285620 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e285620
        have b2e286164 : y = (k (τ y) y) ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e286033
             have i₂ := b2e13 y
             grind)
          | exact superpose b2e13 b2e286033
          | exact resolve b2e286033 b2e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e286033
        have b2e292029 : x = (M.op y x) ∨ y = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e571 y y
             have i₂ := b2e286051
             grind)
          | exact superpose b2e286051 b2e571
          | exact resolve b2e571 b2e286051
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e286051
        have b2e292043 : x = y ∨ y = (σ y) ∨ x = y := by
          first
          | (have i₁ := b2e292029
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e292029
          | exact resolve b2e292029 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e292029
        have b2e292044 : y = (σ y) ∨ x = y := by grind
        clear b2e292043
        have b2e299841 : (σ (M.op x y)) ≠ (M.op (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b2e19
             have i₂ := b2e292044
             grind)
          | exact superpose b2e292044 b2e19
          | exact resolve b2e19 b2e292044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e299844 : ∀ X0 : G, (σ (k y X0)) = (k y (σ X0)) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e18 y X0
             have i₂ := b2e292044
             grind)
          | exact superpose b2e292044 b2e18
          | exact resolve b2e18 b2e292044
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e292044
        have b2e299905 : (σ (M.op y y)) ≠ (M.op (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b2e299841
             have i₂ := b2e33
             grind)
          | exact superpose b2e33 b2e299841
          | exact resolve b2e299841 b2e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e33 b2e299841
        have b2e299913 : (M.op y y) ≠ (M.op (σ x) y) ∨ x = y := by
          first
          | (have i₁ := b2e299905
             have i₂ := b2e34328
             grind)
          | exact superpose b2e34328 b2e299905
          | exact resolve b2e299905 b2e34328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299905
        have b2e314903 : ∀ X0 : G, (k y X0) = (σ (k y (τ X0))) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e299844 (τ X0)
             have i₂ := b2e14 X0
             grind)
          | exact superpose b2e14 b2e299844
          | exact resolve b2e299844 b2e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299844
        have b2e314952 : ∀ X0 : G, (k (σ y) X0) = (k y X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e314903 X0
             have i₂ := b2e25 X0 y
             grind)
          | exact superpose b2e25 b2e314903
          | exact resolve b2e314903 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e314903
        have b2e316106 : (M.op (σ y) (σ y)) = (k y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e51832 (σ y)
             have i₂ := b2e314952 (σ y)
             grind)
          | exact superpose b2e314952 b2e51832
          | exact resolve b2e51832 b2e314952
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51832 b2e314952
        have b2e316197 : (σ (M.op y y)) = (k y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e316106
             have i₂ := b2e45957 y
             grind)
          | exact superpose b2e45957 b2e316106
          | exact resolve b2e316106 b2e45957
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e45957 b2e316106
        have b2e316254 : (M.op y y) = (k y (σ y)) ∨ x = y := by
          first
          | (have i₁ := b2e316197
             have i₂ := b2e34328
             grind)
          | exact superpose b2e34328 b2e316197
          | exact resolve b2e316197 b2e34328
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34328 b2e316197
        have b2e317681 : (τ (M.op y y)) = (k (τ y) y) ∨ x = y := by
          first
          | (have i₁ := b2e62 y y
             have i₂ := b2e316254
             grind)
          | exact superpose b2e316254 b2e62
          | exact resolve b2e62 b2e316254
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e62 b2e316254
        have b2e317696 : (M.op y y) = (k (τ y) y) ∨ x = y := by
          first
          | (have i₁ := b2e317681
             have i₂ := b2e34335
             grind)
          | exact superpose b2e34335 b2e317681
          | exact resolve b2e317681 b2e34335
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34335 b2e317681
        have b2e361691 : y = (M.op y y) ∨ x = y ∨ x = (M.op y y) ∨ x = y := by
          first
          | (have i₁ := b2e317696
             have i₂ := b2e286164
             grind)
          | exact superpose b2e286164 b2e317696
          | exact resolve b2e317696 b2e286164
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e286164 b2e317696
        have b2e361709 : x = (M.op y y) ∨ x = y ∨ y = (M.op y y) := by grind
        clear b2e361691
        have b2e362345 : x = (M.op y x) ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e571 y y
             have i₂ := b2e361709
             grind)
          | exact superpose b2e361709 b2e571
          | exact resolve b2e571 b2e361709
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e571 b2e361709
        have b2e362364 : x = y ∨ x = y ∨ y = (M.op y y) := by
          first
          | (have i₁ := b2e362345
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e362345
          | exact resolve b2e362345 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e362345
        have b2e362365 : y = (M.op y y) ∨ x = y := by grind
        clear b2e362364
        have b2e363489 : ∀ X0 : G, y = (M.op X0 y) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e619 x
             have i₂ := b2e362365
             grind)
          | exact superpose b2e362365 b2e619
          | exact resolve b2e619 b2e362365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e619
        have b2e363497 : ∀ X0 : G, y = (M.op y X0) ∨ x = y := by
          intro X0
          first
          | (have i₁ := b2e996 x
             have i₂ := b2e362365
             grind)
          | exact superpose b2e362365 b2e996
          | exact resolve b2e996 b2e362365
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e996 b2e362365
        have b2e365554 : y ≠ (M.op y y) ∨ x = y ∨ x = y := by
          first
          | (have i₁ := b2e299913
             have i₂ := b2e363489 (σ x)
             grind)
          | exact superpose b2e363489 b2e299913
          | exact resolve b2e299913 b2e363489
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e299913 b2e363489
        have b2e365685 : y ≠ (M.op y y) ∨ x = y := by grind
        clear b2e365554
        have b2e365727 : x = y := by
          first
          | (have r₁ := b2e365685
             have r₂ := b2e363497 y
             grind)
          | exact resolve b2e365685 b2e363497
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e363497 b2e365685
        have b2e367101 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1662
             have i₂ := b2e365727
             grind)
          | exact superpose b2e365727 b2e1662
          | exact resolve b2e1662 b2e365727
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1662 b2e365727
        have b2e367106 : False := by grind
        exact b2e367106
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = y := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e27 : (σ y) ≠ (σ (M.op y y)) := by grind
        have b3e52 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
        have b3e56 : (σ y) = (k (σ y) (σ y)) := by grind
        clear b3e52
        have b3e59 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e56
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e56
          | exact resolve b3e56 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e69 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
        clear b3e59
        have b3e70 : y = (M.op y y) := by
          first
          | (have r₁ := b3e69
             have r₂ := b3e27
             grind)
          | exact resolve b3e69 b3e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e27 b3e69
        have b3e72 : False := by grind
        exact b3e72
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = y := by grind
          have b4e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e61 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b4e951 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
          clear b4e61
          have b4e980 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
          clear b4e951
          have b4e984 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
          clear b4e980
          have b4e985 : y = (M.op y y) := by grind
          clear b4e984
          have b4e986 : False := by grind
          exact b4e986
        · have b5e22 : x = y := by grind
          have b5e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : False := by grind
          exact b5e30
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X1 X2) X1) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ y := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b6e26 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ y) X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op X0 X2) (M.op (M.op X0 X1) X0)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 (M.op X0 X2) X2 X3
             have i₂ := b6e12 X2 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e28 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X1 (M.op X1 X2) X3
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e29 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X3) X0) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e12 x X0 X3
             have i₂ := b6e12 x X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e30 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e31 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e12 X2 X3 (M.op X0 X3)
             have i₂ := b6e12 X3 X0 X1
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e33 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e12 X0 X1 x
             have i₂ := b6e12 X2 X1 x
             grind)
          | exact superpose b6e12 b6e12
          | exact resolve b6e12 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
        have b6e38 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
        have b6e40 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X1 X2) ∨ (M.op X1 X1) = (k X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e15 X1 (M.op X1 X2)
             have i₂ := b6e12 X0 X1 X2
             grind)
          | exact superpose b6e12 b6e15
          | (have j0 := b6e15 X1 (M.op X1 X2)
             grind)
          | (have r₁ := b6e15 (M.op X1 (M.op (M.op X1 X2) X1)) (M.op (M.op X1 X2) X1)
             have r₂ := b6e12 (M.op (M.op X1 X2) X1) X1 X2
             grind)
          | (have r₁ := b6e15 X0 (M.op X0 (M.op X0 X0))
             have r₂ := b6e12 X0 X0 (M.op X0 X0)
             grind)
          | exact resolve b6e15 b6e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e41 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b6e38
        have b6e42 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b6e41
             have i₂ := b6e18 x y
             grind)
          | exact superpose b6e18 b6e41
          | exact resolve b6e41 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e41
        have b6e52 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
          intro X0
          grind
        have b6e58 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ (k x y)) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ x) (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e59 : ∀ X0 : G, (M.op (M.op (σ x) X0) (σ x)) = (M.op (σ x) (σ (k x y))) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) (σ x) X0
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e12
          | exact resolve b6e12 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
        have b6e86 : ∀ X0 : G, (M.op (σ (k x y)) (σ x)) = (M.op (M.op (σ x) X0) (σ x)) := by
          intro X0
          first
          | (have i₁ := b6e29 (σ x) X0 (σ x)
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e29
          | exact resolve b6e29 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e102 : (M.op (σ (k x y)) (σ x)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e86 x
             have i₂ := b6e59 x
             grind)
          | exact superpose b6e59 b6e86
          | exact resolve b6e86 b6e59
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e59 b6e86
        have b6e130 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ y) X0)) := by
          intro X0
          first
          | (have i₁ := b6e33 X0 (σ y) (σ x)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e33
          | exact resolve b6e33 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e153 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e130 x
             have i₂ := b6e30 x
             grind)
          | exact superpose b6e30 b6e130
          | exact resolve b6e130 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e130
        have b6e184 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e29 X0 X1 (M.op (σ y) X0)
             have i₂ := b6e30 X0
             grind)
          | exact superpose b6e30 b6e29
          | exact resolve b6e29 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e187 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e19
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e19
          | exact resolve b6e19 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e194 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) (M.op (σ y) (σ y))) := by
          intro X0
          first
          | (have i₁ := b6e33 X0 (σ x) (σ y)
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e33
          | exact resolve b6e33 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e195 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) X0)) := by
          intro X0
          first
          | (have i₁ := b6e194 X0
             have i₂ := b6e30 (σ y)
             grind)
          | exact superpose b6e30 b6e194
          | exact resolve b6e194 b6e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e194
        have b6e215 : ∀ X0 X1 : G, (M.op (σ y) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (σ y) X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e33 X0 (M.op (σ y) X1) (σ y)
             have i₂ := b6e26 X1
             grind)
          | exact superpose b6e26 b6e33
          | exact resolve b6e33 b6e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e216 : ∀ X0 X1 : G, (M.op (σ (k x y)) (σ x)) = (M.op X0 (M.op (M.op (σ y) X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e215 X0 X1
             have i₂ := b6e58 (σ y)
             grind)
          | exact superpose b6e58 b6e215
          | exact resolve b6e215 b6e58
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e215
        have b6e227 : ∀ X0 X1 : G, (M.op (σ x) (σ (k x y))) = (M.op X0 (M.op (M.op (σ y) X1) X0)) := by
          intro X0 X1
          first
          | (have i₁ := b6e216 X0 X1
             have i₂ := b6e102
             grind)
          | exact superpose b6e102 b6e216
          | exact resolve b6e216 b6e102
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e102 b6e216
        have b6e295 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ y) (M.op (M.op X1 X2) X1)) X0)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e30 (M.op (M.op X1 X2) X1)
             have i₂ := b6e31 X1 X2 X0 (M.op (σ y) (M.op (M.op X1 X2) X1))
             grind)
          | exact superpose b6e31 b6e30
          | exact resolve b6e30 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e30
        have b6e296 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ (k x y))) := by
          first
          | (have i₁ := b6e295 x x x
             have i₂ := b6e227 x (M.op (M.op x x) x)
             grind)
          | exact superpose b6e227 b6e295
          | exact resolve b6e295 b6e227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e295
        have b6e339 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (σ y)) X0) = (M.op (M.op X1 X0) (M.op (M.op X1 X2) X1)) := by
          intro X0 X1 X2
          first
          | (have i₁ := b6e27 X1 X2 X0 (M.op (σ x) X0)
             have i₂ := b6e195 X0
             grind)
          | exact superpose b6e195 b6e27
          | exact resolve b6e27 b6e195
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e358 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e27 X2 X4 (M.op X1 X2) X3
             have i₂ := b6e33 X2 X1 X0
             grind)
          | (have i₁ := b6e27 X2 X4 (M.op X1 X2) X3
             have i₂ := b6e33 X0 X1 X2
             grind)
          | exact superpose b6e33 b6e27
          | exact resolve b6e27 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e399 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X3) X4) (M.op X1 X3)) = (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e12 X1 (M.op X1 X3) X4
             have i₂ := b6e27 X0 X2 X1 X3
             grind)
          | exact superpose b6e27 b6e12
          | exact resolve b6e12 b6e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27
        have b6e422 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X0 X1) (M.op (M.op X0 X2) X0))) = (M.op (M.op (σ y) (σ y)) (M.op X1 X3)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e399 X0 X1 X2 X3 x
             have i₂ := b6e184 (M.op X1 X3) x
             grind)
          | exact superpose b6e184 b6e399
          | exact resolve b6e399 b6e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e399
        have b6e438 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op (M.op X2 X4) X2)) = (M.op (M.op (σ y) (σ y)) (M.op X1 X2)) := by
          intro X0 X1 X2 X4
          first
          | (have i₁ := b6e358 X0 X1 X2 x X4
             have i₂ := b6e184 (M.op X1 X2) x
             grind)
          | exact superpose b6e184 b6e358
          | exact resolve b6e358 b6e184
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e184 b6e358
        have b6e449 : ∀ X1 X3 : G, (M.op (M.op (σ y) (σ y)) (M.op X1 X3)) = (M.op X1 (M.op (M.op (σ y) (σ y)) X1)) := by
          intro X1 X3
          first
          | (have i₁ := b6e422 x X1 x X3
             have i₂ := b6e339 X1 x x
             grind)
          | exact superpose b6e339 b6e422
          | exact resolve b6e422 b6e339
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e339 b6e422
        have b6e455 : ∀ X1 X3 : G, (M.op (σ x) (σ (k x y))) = (M.op (M.op (σ y) (σ y)) (M.op X1 X3)) := by
          intro X1 X3
          first
          | (have i₁ := b6e449 X1 X3
             have i₂ := b6e227 X1 (σ y)
             grind)
          | exact superpose b6e227 b6e449
          | exact resolve b6e449 b6e227
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e227 b6e449
        have b6e458 : ∀ X1 X3 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) (σ y)) (M.op X1 X3)) := by
          intro X1 X3
          first
          | (have i₁ := b6e455 X1 X3
             have i₂ := b6e296
             grind)
          | exact superpose b6e296 b6e455
          | exact resolve b6e455 b6e296
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e296 b6e455
        have b6e587 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op X4 (M.op X0 X4)) (M.op (M.op (M.op X0 X1) X2) (M.op X0 X1))) := by
          intro X0 X1 X2 X3 X4
          first
          | (have i₁ := b6e33 X3 X0 (M.op X4 (M.op X0 X4))
             have i₂ := b6e28 X4 X0 X1 X2
             grind)
          | exact superpose b6e28 b6e33
          | exact resolve b6e33 b6e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e28
        have b6e597 : ∀ X0 X1 X3 : G, (M.op X3 (M.op X0 X3)) = (M.op (M.op (σ y) (σ y)) (M.op X0 (M.op X0 X1))) := by
          intro X0 X1 X3
          first
          | (have i₁ := b6e587 X0 X1 x X3 x
             have i₂ := b6e438 x X0 (M.op X0 X1) x
             grind)
          | exact superpose b6e438 b6e587
          | exact resolve b6e587 b6e438
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e438 b6e587
        have b6e655 : ∀ X0 X3 : G, (M.op (σ y) (σ y)) = (M.op X3 (M.op X0 X3)) := by
          intro X0 X3
          first
          | (have i₁ := b6e597 X0 x X3
             have i₂ := b6e458 X0 (M.op X0 x)
             grind)
          | exact superpose b6e458 b6e597
          | exact resolve b6e597 b6e458
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e458 b6e597
        have b6e733 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op X2 (M.op X3 X2)) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e655 X3 X2
             have i₂ := b6e655 X1 X0
             grind)
          | exact superpose b6e655 b6e655
          | exact resolve b6e655 b6e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e760 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (σ (M.op x y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e187
             have i₂ := b6e655 X1 X0
             grind)
          | exact superpose b6e655 b6e187
          | exact resolve b6e187 b6e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e766 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (σ y) ∨ (M.op X0 (M.op X1 X0)) = (k (σ y) (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e655 X0 x
             grind)
          | exact superpose b6e655 b6e15
          | (have r₁ := b6e15 (M.op X0 (M.op (σ y) (σ y))) (M.op (σ y) (σ y))
             have r₂ := b6e655 X0 (M.op (σ y) (σ y))
             grind)
          | exact resolve b6e15 b6e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e813 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (σ y) ∨ (M.op X0 (M.op X1 X0)) = (σ (k y y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e766 X0 X1
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e766
          | (have j0 := b6e766 X0 X1
             grind)
          | exact resolve b6e766 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e766
        have b6e1153 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) ≠ (M.op X2 (M.op X3 X2)) ∨ (M.op X3 X3) = (k X3 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X2 X3
          first
          | (have i₁ := b6e40 X0 X0 (M.op X1 X0)
             have i₂ := b6e33 X0 X1 X2
             grind)
          | (have i₁ := b6e40 X0 X2 (M.op X1 X2)
             have i₂ := b6e33 X0 X1 X2
             grind)
          | exact superpose b6e33 b6e40
          | (have r₁ := b6e40 X0 X2 (M.op X2 X2)
             have r₂ := b6e33 X0 X2 X2
             grind)
          | (have r₁ := b6e40 X2 X0 (M.op X0 X0)
             have r₂ := b6e33 X0 X0 X2
             grind)
          | exact resolve b6e40 b6e33
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e33
        have b6e1167 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 (M.op X0 X0))) := by
          intro X0
          first
          | (have j0 := b6e40 X0 X0 (M.op X0 X0)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1175 : ∀ X0 X1 X3 : G, (M.op X3 X3) = (k X3 (M.op X0 (M.op X1 X0))) := by
          intro X0 X1 X3
          first
          | (have j0 := b6e1153 X0 X1 x X3
             grind)
          | (have r₁ := b6e1153 X0 X1 x X3
             have r₂ := b6e733 X0 X1 x X3
             grind)
          | (have r₁ := b6e1153 x X3 X0 X1
             have r₂ := b6e733 X0 X1 x X3
             grind)
          | exact resolve b6e1153 b6e733
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1153
        have b6e1316 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (k y y)) ∨ (M.op X0 (M.op X1 X0)) = (σ y) := by
          intro X0 X1
          first
          | (have i₁ := b6e52 y
             have i₂ := b6e655 X0 x
             grind)
          | exact superpose b6e655 b6e52
          | exact resolve b6e52 b6e655
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e1362 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (σ (k y y)) := by
          intro X0 X1
          first
          | (have j0 := b6e1316 X0 X1
             have j1 := b6e813 X0 X1
             grind)
          | (have r₁ := b6e1316 X0 X1
             have r₂ := b6e813 X0 X1
             grind)
          | exact resolve b6e1316 b6e813
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e813 b6e1316
        have b6e1503 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e153
             have i₂ := b6e62 y x
             grind)
          | exact superpose b6e62 b6e153
          | (have j1 := b6e62 y x
             grind)
          | exact resolve b6e153 b6e62
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e62 b6e153
        have b6e1551 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1503
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e1503
          | exact resolve b6e1503 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1503
        have b6e1607 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X1 X0))) = (σ (k y y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e1362 X1 (M.op (M.op x x) x)
             have i₂ := b6e31 x x X0 X1
             grind)
          | exact superpose b6e31 b6e1362
          | exact resolve b6e1362 b6e31
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e31
        have b6e1623 : ∀ X1 X2 : G, (M.op (M.op X1 X2) X1) = (σ (k y y)) := by
          intro X1 X2
          first
          | (have i₁ := b6e12 x X1 X2
             have i₂ := b6e1362 x X1
             grind)
          | exact superpose b6e1362 b6e12
          | exact resolve b6e12 b6e1362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e1633 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e195 x
             have i₂ := b6e1362 x (σ x)
             grind)
          | exact superpose b6e1362 b6e195
          | exact resolve b6e195 b6e1362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e195
        have b6e1653 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ (σ (k y y)) ∨ (M.op X1 X1) = (k X1 (σ (k y y))) := by
          intro X0 X1
          first
          | (have i₁ := b6e40 X0 X0 (M.op X1 X0)
             have i₂ := b6e1362 X0 X1
             grind)
          | exact superpose b6e1362 b6e40
          | exact resolve b6e40 b6e1362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e40
        have b6e1668 : ∀ X1 : G, (M.op X1 X1) = (k X1 (σ (k y y))) := by
          intro X1
          first
          | (have j0 := b6e1653 x X1
             grind)
          | (have r₁ := b6e1653 x X1
             have r₂ := b6e1362 x X1
             grind)
          | exact resolve b6e1653 b6e1362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1653
        have b6e1694 : ∀ X1 : G, (σ (k y y)) = (M.op X1 (σ (k y y))) := by
          intro X1
          first
          | (have i₁ := b6e1607 x X1
             have i₂ := b6e1362 x X1
             grind)
          | exact superpose b6e1362 b6e1607
          | exact resolve b6e1607 b6e1362
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1607
        have b6e2893 : (σ (k y y)) = (k (σ y) (M.op (σ y) (σ (k y y)))) := by
          first
          | (have i₁ := b6e1167 (σ y)
             have i₂ := b6e1633
             grind)
          | exact superpose b6e1633 b6e1167
          | exact resolve b6e1167 b6e1633
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1167 b6e1633
        have b6e2894 : (σ (k y y)) = (k (σ y) (σ (k y y))) := by
          first
          | (have i₁ := b6e2893
             have i₂ := b6e1694 (σ y)
             grind)
          | exact superpose b6e1694 b6e2893
          | exact resolve b6e2893 b6e1694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2893
        have b6e2913 : (σ (k y y)) = (σ (k y (k y y))) := by
          first
          | (have i₁ := b6e2894
             have i₂ := b6e18 y (k y y)
             grind)
          | exact superpose b6e18 b6e2894
          | exact resolve b6e2894 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2894
        have b6e3331 : ∀ X0 : G, (k (τ X0) (k y y)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e37 X0 (k y y)
             have i₂ := b6e1668 X0
             grind)
          | exact superpose b6e1668 b6e37
          | exact resolve b6e37 b6e1668
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37 b6e1668
        have b6e5513 : (τ (σ (k y y))) = (k y (k y y)) := by
          first
          | (have i₁ := b6e13 (k y (k y y))
             have i₂ := b6e2913
             grind)
          | exact superpose b6e2913 b6e13
          | exact resolve b6e13 b6e2913
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e5530 : (k y y) = (k y (k y y)) := by
          first
          | (have i₁ := b6e5513
             have i₂ := b6e13 (k y y)
             grind)
          | exact superpose b6e13 b6e5513
          | exact resolve b6e5513 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5513
        have b6e6037 : (τ (σ (k y y))) = (k (τ (σ (k y y))) (k y y)) := by
          first
          | (have i₁ := b6e3331 (σ (k y y))
             have i₂ := b6e1694 (σ (k y y))
             grind)
          | exact superpose b6e1694 b6e3331
          | exact resolve b6e3331 b6e1694
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1694
        have b6e6059 : (k y y) = (k (k y y) (k y y)) := by
          first
          | (have i₁ := b6e6037
             have i₂ := b6e13 (k y y)
             grind)
          | exact superpose b6e13 b6e6037
          | exact resolve b6e6037 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6037
        have b6e6412 : (k y y) = (M.op (k y y) (k y y)) ∨ (k y y) = (M.op (k y y) (k y y)) := by grind
        clear b6e6059
        have b6e6413 : (k y y) = (M.op (k y y) (k y y)) := by grind
        clear b6e6412
        have b6e6665 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op (k y y) (k y y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e733 X0 X1 (k y y) (k y y)
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e733
          | exact resolve b6e733 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e733
        have b6e6667 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (k y y) (k y y))) := by
          intro X0
          first
          | (have i₁ := b6e1175 (k y y) (k y y) X0
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e1175
          | exact resolve b6e1175 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1175
        have b6e6669 : (σ (k y y)) = (M.op (k y y) (k y y)) := by
          first
          | (have i₁ := b6e1623 (k y y) (k y y)
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e1623
          | exact resolve b6e1623 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1623
        have b6e6671 : (k y y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e6669
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e6669
          | exact resolve b6e6669 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6669
        have b6e6673 : ∀ X0 : G, (M.op X0 X0) = (k X0 (k y y)) := by
          intro X0
          first
          | (have i₁ := b6e6667 X0
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e6667
          | exact resolve b6e6667 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6667
        have b6e6675 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k y y) := by
          intro X0 X1
          first
          | (have i₁ := b6e6665 X0 X1
             have i₂ := b6e6413
             grind)
          | exact superpose b6e6413 b6e6665
          | exact resolve b6e6665 b6e6413
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6413 b6e6665
        have b6e7168 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (k X0 (k y y))) := by
          intro X0
          first
          | (have i₁ := b6e760 X0 X0
             have i₂ := b6e6673 X0
             grind)
          | exact superpose b6e6673 b6e760
          | exact resolve b6e760 b6e6673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e760
        have b6e7170 : ∀ X0 : G, (σ (k y y)) = (M.op X0 (k X0 (k y y))) := by
          intro X0
          first
          | (have i₁ := b6e1362 X0 X0
             have i₂ := b6e6673 X0
             grind)
          | exact superpose b6e6673 b6e1362
          | exact resolve b6e1362 b6e6673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1362
        have b6e7187 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e3331 X0
             have i₂ := b6e6673 (τ X0)
             grind)
          | exact superpose b6e6673 b6e3331
          | exact resolve b6e3331 b6e6673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e3331
        have b6e7190 : (k y y) = (M.op y y) := by
          first
          | (have i₁ := b6e5530
             have i₂ := b6e6673 y
             grind)
          | exact superpose b6e6673 b6e5530
          | exact resolve b6e5530 b6e6673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e5530
        have b6e7191 : (σ (k y y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e2913
             have i₂ := b6e6673 y
             grind)
          | exact superpose b6e6673 b6e2913
          | exact resolve b6e2913 b6e6673
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2913 b6e6673
        have b6e7192 : (k y y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7191
             have i₂ := b6e6671
             grind)
          | exact superpose b6e6671 b6e7191
          | exact resolve b6e7191 b6e6671
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e6671 b6e7191
        have b6e7209 : ∀ X0 : G, (σ (M.op y y)) = (M.op X0 (k X0 (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b6e7170 X0
             have i₂ := b6e7190
             grind)
          | exact superpose b6e7190 b6e7170
          | exact resolve b6e7170 b6e7190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7170
        have b6e7211 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op X0 (k X0 (M.op y y))) := by
          intro X0
          first
          | (have i₁ := b6e7168 X0
             have i₂ := b6e7190
             grind)
          | exact superpose b6e7190 b6e7168
          | exact resolve b6e7168 b6e7190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7168
        have b6e7262 : (M.op y y) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7192
             have i₂ := b6e7190
             grind)
          | exact superpose b6e7190 b6e7192
          | exact resolve b6e7192 b6e7190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7192
        have b6e7275 : (σ (M.op x y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b6e7211 x
             have i₂ := b6e7209 x
             grind)
          | exact superpose b6e7209 b6e7211
          | exact resolve b6e7211 b6e7209
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7209 b6e7211
        have b6e7333 : (σ (M.op x y)) ≠ (M.op y y) := by
          first
          | (have i₁ := b6e7275
             have i₂ := b6e7262
             grind)
          | exact superpose b6e7262 b6e7275
          | exact resolve b6e7275 b6e7262
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7262 b6e7275
        have b6e10031 : (M.op (σ (k x y)) (σ x)) = (k y y) := by
          first
          | (have i₁ := b6e58 x
             have i₂ := b6e6675 x (σ x)
             grind)
          | exact superpose b6e6675 b6e58
          | exact resolve b6e58 b6e6675
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e58 b6e6675
        have b6e10146 : (M.op (σ (k x y)) (σ x)) = (M.op y y) := by
          first
          | (have i₁ := b6e10031
             have i₂ := b6e7190
             grind)
          | exact superpose b6e7190 b6e10031
          | exact resolve b6e10031 b6e7190
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7190 b6e10031
        have b6e26854 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
          intro X0
          first
          | (have i₁ := b6e7187 (σ X0)
             have i₂ := b6e13 X0
             grind)
          | exact superpose b6e13 b6e7187
          | exact resolve b6e7187 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7187
        have b6e27499 : (M.op x x) = (τ (σ (k x y))) := by
          first
          | (have i₁ := b6e26854 x
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e26854
          | exact resolve b6e26854 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27513 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b6e14 (M.op (σ X0) (σ X0))
             have i₂ := b6e26854 X0
             grind)
          | exact superpose b6e26854 b6e14
          | exact resolve b6e14 b6e26854
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26854
        have b6e27532 : (k x y) = (M.op x x) := by
          first
          | (have i₁ := b6e27499
             have i₂ := b6e13 (k x y)
             grind)
          | exact superpose b6e13 b6e27499
          | exact resolve b6e27499 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27499
        have b6e27657 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e27532
             grind)
          | exact superpose b6e27532 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e27532
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e27658 : (M.op x y) = (M.op x x) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e27657
             have r₂ := b6e21
             grind)
          | exact resolve b6e27657 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27657
        have b6e27663 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e27658
             have r₂ := b6e20
             grind)
          | exact resolve b6e27658 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27658
        have b6e37672 : (M.op y y) = (M.op (σ (M.op x y)) (σ x)) ∨ x = y ∨ y = (M.op y x) := by
          first
          | (have i₁ := b6e10146
             have i₂ := b6e17 x y
             grind)
          | exact superpose b6e17 b6e10146
          | (have j1 := b6e17 x y
             grind)
          | exact resolve b6e10146 b6e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e10146
        have b6e37805 : (M.op y y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
          first
          | (have r₁ := b6e37672
             have r₂ := b6e21
             grind)
          | exact resolve b6e37672 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37672
        have b6e37846 : (M.op y y) = (M.op (σ (M.op x y)) (σ x)) := by
          first
          | (have r₁ := b6e37805
             have r₂ := b6e20
             grind)
          | exact resolve b6e37805 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37805
        have b6e435547 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e655 (σ y) (σ y)
             have i₂ := b6e1551
             grind)
          | exact superpose b6e1551 b6e655
          | exact resolve b6e655 b6e1551
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e655 b6e1551
        have b6e435630 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e435547
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e435547
          | exact resolve b6e435547 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435547
        have b6e435631 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
        clear b6e435630
        have b6e435884 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k y x)
             have i₂ := b6e435631
             grind)
          | exact superpose b6e435631 b6e13
          | exact resolve b6e13 b6e435631
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435631
        have b6e436023 : y = (k y x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e435884
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e435884
          | exact resolve b6e435884 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e435884
        have b6e438279 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 y x
             have i₂ := b6e436023
             grind)
          | exact superpose b6e436023 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e436023
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e436023
        have b6e438299 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e438279
             have r₂ := b6e20
             grind)
          | exact resolve b6e438279 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e438279
        have b6e438302 : x = (M.op x y) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e438299
             have r₂ := b6e21
             grind)
          | exact resolve b6e438299 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e438299
        have b6e439453 : (M.op (σ x) (σ x)) = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e37846
             have i₂ := b6e438302
             grind)
          | exact superpose b6e438302 b6e37846
          | exact resolve b6e37846 b6e438302
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e37846 b6e438302
        have b6e439828 : (σ (k x y)) = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e439453
             have i₂ := b6e42
             grind)
          | exact superpose b6e42 b6e439453
          | exact resolve b6e439453 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e439453
        have b6e439948 : (σ (M.op x x)) = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e439828
             have i₂ := b6e27532
             grind)
          | exact superpose b6e27532 b6e439828
          | exact resolve b6e439828 b6e27532
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27532 b6e439828
        have b6e440029 : (σ (M.op x y)) = (M.op y y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e439948
             have i₂ := b6e27663
             grind)
          | exact superpose b6e27663 b6e439948
          | exact resolve b6e439948 b6e27663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e439948
        have b6e440086 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e440029
             have r₂ := b6e7333
             grind)
          | exact resolve b6e440029 b6e7333
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e7333 b6e440029
        have b6e440214 : (M.op (σ y) (σ y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b6e27513 x
             have i₂ := b6e440086
             grind)
          | exact superpose b6e440086 b6e27513
          | exact resolve b6e27513 b6e440086
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27513 b6e440086
        have b6e440233 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
          first
          | (have i₁ := b6e440214
             have i₂ := b6e27663
             grind)
          | exact superpose b6e27663 b6e440214
          | exact resolve b6e440214 b6e27663
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e27663 b6e440214
        have b6e440302 : False := by grind
        exact b6e440302
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e22 : x ≠ y := by grind
          have b7e24 : (σ x) = (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e28 : x = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 x
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e14
            | exact resolve b7e14 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e29 : x = y := by
            first
            | (have i₁ := b7e28
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e28
            | exact resolve b7e28 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e30 : False := by grind
          exact b7e30
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y x) := by grind
          have b8e22 : x ≠ y := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e1096 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e79 x y
               grind)
            | exact superpose b8e79 b8e20
            | (have j1 := b8e79 x y
               grind)
            | exact resolve b8e20 b8e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e79
          have b8e1161 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
            first
            | (have r₁ := b8e1096
               have r₂ := b8e23
               grind)
            | exact resolve b8e1096 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1096
          have b8e1166 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e1161
               have r₂ := b8e24
               grind)
            | exact resolve b8e1161 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1161
          have b8e1167 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
            first
            | (have i₁ := b8e1166
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1166
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e1166
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e1166
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e1166 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1166
          have b8e1168 : x = y ∨ y = (M.op y x) := by grind
          clear b8e1167
          have b8e1169 : y = (M.op y x) := by
            first
            | (have r₁ := b8e1168
               have r₂ := b8e22
               grind)
            | exact resolve b8e1168 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1168
          have b8e1170 : False := by grind
          exact b8e1170

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if X = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxx_pyx_pxy_Equation4456 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
          intro X0 X1
          grind
        have b0e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y x) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e33 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e12 X0 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e34 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
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
        have b0e35 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e33 X0
             have i₂ := b0e34 X0
             grind)
          | exact superpose b0e34 b0e33
          | exact resolve b0e33 b0e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e33 b0e34
        have b0e39 : y = (M.op x x) := by
          first
          | (have i₁ := b0e20
             have i₂ := b0e35 x
             grind)
          | exact superpose b0e35 b0e20
          | exact resolve b0e20 b0e35
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e35
        have b0e40 : x = y := by
          first
          | (have i₁ := b0e39
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e39
          | exact resolve b0e39 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e39
        have b0e47 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e15 (σ x) (σ y)
             have i₂ := b0e21
             grind)
          | exact superpose b0e21 b0e15
          | (have j0 := b0e15 (σ x) (σ y)
             grind)
          | (have r₁ := b0e15 (σ x) (σ y)
             have r₂ := b0e21
             grind)
          | exact resolve b0e15 b0e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e49 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b0e15 x x
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e15
          | (have r₁ := b0e15 x x
             have r₂ := b0e22
             grind)
          | exact resolve b0e15 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e50 : x = (k x x) := by grind
        clear b0e49
        have b0e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear b0e47
        have b0e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b0e52
             have i₂ := b0e18 x y
             grind)
          | exact superpose b0e18 b0e52
          | exact resolve b0e52 b0e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e52
        have b0e57 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b0e54
             have i₂ := b0e40
             grind)
          | exact superpose b0e40 b0e54
          | exact resolve b0e54 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54
        have b0e59 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e57
             have i₂ := b0e50
             grind)
          | exact superpose b0e50 b0e57
          | exact resolve b0e57 b0e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e50 b0e57
        have b0e60 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e40
             grind)
          | exact superpose b0e40 b0e19
          | exact resolve b0e19 b0e40
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e40
        have b0e63 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e60
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e60
          | exact resolve b0e60 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e60
        have b0e64 : False := by grind
        exact b0e64
      · rcases eq_or_ne (x) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b1e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : y = (M.op y x) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e29 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X0 (M.op X2 X1) X3
               have i₂ := b1e13 X0 X1 X2
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 X1 X3
               have i₂ := b1e13 X2 X1 X0
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e33 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X2 X0 (M.op x X1)
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e34 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 (σ x) (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e35 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e36 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b1e35 (M.op x x)
               have i₂ := b1e35 x
               grind)
            | exact superpose b1e35 b1e35
            | exact resolve b1e35 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 x X1
               have i₂ := b1e35 X0
               grind)
            | exact superpose b1e35 b1e13
            | exact resolve b1e13 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e39 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 (M.op x X0) X0
               have i₂ := b1e35 X0
               grind)
            | exact superpose b1e35 b1e13
            | exact resolve b1e13 b1e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35
          have b1e41 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b1e36
               have i₂ := b1e38 (M.op y x) x
               grind)
            | exact superpose b1e38 b1e36
            | exact resolve b1e36 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e36
          have b1e42 : (M.op y (M.op x x)) = (M.op y y) := by
            first
            | (have i₁ := b1e41
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e41
            | exact resolve b1e41 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e41
          have b1e46 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
          have b1e47 : y ≠ y ∨ (M.op x x) = (k x y) := by
            first
            | (have i₁ := b1e16 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e16
            | (have j0 := b1e16 x y
               grind)
            | (have r₁ := b1e16 x y
               have r₂ := b1e21
               grind)
            | exact resolve b1e16 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e48 : (M.op x x) = (k x y) := by grind
          clear b1e47
          have b1e49 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b1e46
          have b1e50 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b1e49
               have i₂ := b1e19 x y
               grind)
            | exact superpose b1e19 b1e49
            | exact resolve b1e49 b1e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e49
          have b1e51 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b1e50
               have i₂ := b1e48
               grind)
            | exact superpose b1e48 b1e50
            | exact resolve b1e50 b1e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e48 b1e50
          have b1e70 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 (M.op x x) y
               have i₂ := b1e42
               grind)
            | exact superpose b1e42 b1e13
            | exact resolve b1e13 b1e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e42
          have b1e73 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e70 X0
               have i₂ := b1e39 x X0
               grind)
            | exact superpose b1e39 b1e70
            | exact resolve b1e70 b1e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e39 b1e70
          have b1e76 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e73 X0
               have i₂ := b1e38 X0 y
               grind)
            | exact superpose b1e38 b1e73
            | exact resolve b1e73 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38 b1e73
          have b1e92 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 y y
               have i₂ := b1e76 X0
               grind)
            | exact superpose b1e76 b1e13
            | exact resolve b1e13 b1e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e76
          have b1e108 : y = (M.op x y) := by
            first
            | (have i₁ := b1e92 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e92
            | exact resolve b1e92 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e92
          have b1e229 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b1e34 (σ x)
               have i₂ := b1e51
               grind)
            | exact superpose b1e51 b1e34
            | exact resolve b1e34 b1e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e258 : (σ y) = (M.op (σ x) (σ (M.op x x))) := by
            first
            | (have i₁ := b1e229
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e229
            | exact resolve b1e229 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e229
          have b1e381 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X3 (M.op X2 X1)) X0) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e31 X1 (M.op X2 X1) X0 X3
               have i₂ := b1e33 X1 X2 X0
               grind)
            | exact superpose b1e33 b1e31
            | exact resolve b1e31 b1e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e31 b1e33
          have b1e481 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 (σ x))) (σ x)) = (M.op (σ x) (M.op (σ x) (σ (M.op x x)))) := by
            intro X0 X1
            first
            | (have i₁ := b1e29 (σ x) (σ x) X1 X0
               have i₂ := b1e51
               grind)
            | exact superpose b1e51 b1e29
            | exact resolve b1e29 b1e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e29 b1e51
          have b1e552 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b1e481 X0 X1
               have i₂ := b1e258
               grind)
            | exact superpose b1e258 b1e481
            | exact resolve b1e481 b1e258
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e258 b1e481
          have b1e598 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ x))) := by
            first
            | (have i₁ := b1e552 x x
               have i₂ := b1e381 (σ x) (σ x) x x
               grind)
            | exact superpose b1e381 b1e552
            | exact resolve b1e552 b1e381
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e381 b1e552
          have b1e625 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b1e598
               have i₂ := b1e34 (σ x)
               grind)
            | exact superpose b1e34 b1e598
            | exact resolve b1e598 b1e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e34 b1e598
          have b1e644 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e625
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e625
            | exact resolve b1e625 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e625
          have b1e654 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e644
               grind)
            | exact superpose b1e644 b1e20
            | exact resolve b1e20 b1e644
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e644
          have b1e667 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e654
               have i₂ := b1e108
               grind)
            | exact superpose b1e108 b1e654
            | exact resolve b1e654 b1e108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e108 b1e654
          have b1e668 : False := by grind
          exact b1e668
        · have b2e24 : x ≠ x := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : False := by grind
          exact b2e26
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ x) = (σ y) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 y
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e14
            | exact resolve b3e14 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e29 : x = y := by
            first
            | (have i₁ := b3e28
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e28
            | exact resolve b3e28 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e28
          have b3e53 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b3e16 x x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e16
            | (have r₁ := b3e16 x x
               have r₂ := b3e24
               grind)
            | exact resolve b3e16 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e57 : x = (k x x) := by grind
          clear b3e53
          have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b3e1062 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e63 x
               grind)
            | exact superpose b3e63 b3e27
            | (have j1 := b3e63 x
               grind)
            | exact resolve b3e27 b3e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27 b3e63
          have b3e1081 : (σ (M.op x y)) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b3e1062
               have r₂ := b3e26
               grind)
            | exact resolve b3e1062 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e1062
          have b3e1084 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e1081
               have i₂ := b3e57
               grind)
            | exact superpose b3e57 b3e1081
            | exact resolve b3e1081 b3e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e57 b3e1081
          have b3e1087 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e1084
               have i₂ := b3e29
               grind)
            | exact superpose b3e29 b3e1084
            | exact resolve b3e1084 b3e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e29 b3e1084
          have b3e1089 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e1087
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e1087
            | exact resolve b3e1087 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1087
          have b3e1090 : False := by grind
          exact b3e1090
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e24 : (σ x) = (σ y) := by grind
            have b4e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 y
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e15
              | exact resolve b4e15 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e31 : x = y := by
              first
              | (have i₁ := b4e30
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e30
              | exact resolve b4e30 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30
            have b4e32 : x = (M.op x x) := by
              first
              | (have i₁ := b4e22
                 have i₂ := b4e31
                 grind)
              | exact superpose b4e31 b4e22
              | exact resolve b4e22 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31
            have b4e33 : False := by grind
            exact b4e33
          · have b5e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : False := by grind
            exact b5e28
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e23 : (σ x) ≠ (σ y) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e35 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e39 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b6e35 X0
               have i₂ := b6e36 X0
               grind)
            | exact superpose b6e36 b6e35
            | exact resolve b6e35 b6e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35 b6e36
          have b6e43 : y = (M.op x x) := by
            first
            | (have i₁ := b6e21
               have i₂ := b6e39 x
               grind)
            | exact superpose b6e39 b6e21
            | exact resolve b6e21 b6e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e39
          have b6e44 : x = y := by
            first
            | (have i₁ := b6e43
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e43
            | exact resolve b6e43 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e43
          have b6e61 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e44
               grind)
            | exact superpose b6e44 b6e23
            | exact resolve b6e23 b6e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e44
          have b6e63 : False := by grind
          exact b6e63
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op y x) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ x) ≠ (σ y) := by grind
            have b7e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e37 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
              first
              | (have i₁ := b7e37 (M.op x x)
                 have i₂ := b7e37 x
                 grind)
              | exact superpose b7e37 b7e37
              | exact resolve b7e37 b7e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e42 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 x X1
                 have i₂ := b7e37 X0
                 grind)
              | exact superpose b7e37 b7e14
              | exact resolve b7e14 b7e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e43 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (M.op x X0) X0
                 have i₂ := b7e37 X0
                 grind)
              | exact superpose b7e37 b7e14
              | exact resolve b7e14 b7e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37
            have b7e45 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
              first
              | (have i₁ := b7e40
                 have i₂ := b7e42 (M.op y x) x
                 grind)
              | exact superpose b7e42 b7e40
              | exact resolve b7e40 b7e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e46 : (M.op y (M.op x x)) = (M.op y y) := by
              first
              | (have i₁ := b7e45
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e45
              | exact resolve b7e45 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e45
            have b7e47 : y ≠ y ∨ (M.op x x) = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e51 : (M.op x x) = (k x y) := by grind
            clear b7e47
            have b7e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X0 X1
                 have i₂ := b7e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b7e19 b7e20
              | (have j1 := b7e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b7e20 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e73 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 (M.op x x) y
                 have i₂ := b7e46
                 grind)
              | exact superpose b7e46 b7e14
              | exact resolve b7e14 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46
            have b7e76 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e73 X0
                 have i₂ := b7e43 x X0
                 grind)
              | exact superpose b7e43 b7e73
              | exact resolve b7e73 b7e43
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e43 b7e73
            have b7e79 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e76 X0
                 have i₂ := b7e42 X0 y
                 grind)
              | exact superpose b7e42 b7e76
              | exact resolve b7e76 b7e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e42 b7e76
            have b7e99 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y y
                 have i₂ := b7e79 X0
                 grind)
              | exact superpose b7e79 b7e14
              | exact resolve b7e14 b7e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e79
            have b7e158 : y = (M.op x y) := by
              first
              | (have i₁ := b7e99 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e99
              | exact resolve b7e99 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e99
            have b7e1178 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e69 y x
                 grind)
              | exact superpose b7e69 b7e23
              | (have j1 := b7e69 y x
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e69 x y
                 grind)
              | exact resolve b7e23 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1196 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e69 x y
                 grind)
              | exact superpose b7e69 b7e23
              | (have j1 := b7e69 x y
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e69 x y
                 grind)
              | exact resolve b7e23 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e69
            have b7e1216 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b7e1196
            have b7e1221 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b7e1216
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e1216 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1216
            have b7e1224 : (σ y) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have r₁ := b7e1178
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e1178 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1178
            have b7e1229 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
              first
              | (have i₁ := b7e1221
                 have i₂ := b7e51
                 grind)
              | exact superpose b7e51 b7e1221
              | exact resolve b7e1221 b7e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e51 b7e1221
            have b7e13454 : (σ y) ≠ (σ (M.op y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
              first
              | (have i₁ := b7e1224
                 have i₂ := b7e19 y x
                 grind)
              | exact superpose b7e19 b7e1224
              | (have j1 := b7e19 (σ x) (M.op (σ x) (σ y))
                 grind)
              | (have r₁ := b7e1224
                 have r₂ := b7e19 (σ y) (σ (k y x))
                 grind)
              | (have r₁ := b7e1224
                 have r₂ := b7e19 (σ (k y x)) (σ y)
                 grind)
              | exact resolve b7e1224 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1224
            have b7e13455 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
              first
              | (have i₁ := b7e13454
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e13454
              | exact resolve b7e13454 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13454
            have b7e13456 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
            clear b7e13455
            have b7e13457 : (σ x) = (σ (M.op x x)) ∨ x = y ∨ x = (M.op x y) := by
              first
              | (have i₁ := b7e13456
                 have i₂ := b7e1229
                 grind)
              | exact superpose b7e1229 b7e13456
              | exact resolve b7e13456 b7e1229
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1229 b7e13456
            have b7e13458 : x = y ∨ (σ x) = (σ (M.op x x)) ∨ x = y := by
              first
              | (have i₁ := b7e13457
                 have i₂ := b7e158
                 grind)
              | exact superpose b7e158 b7e13457
              | exact resolve b7e13457 b7e158
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e158 b7e13457
            have b7e13459 : (σ x) = (σ (M.op x x)) ∨ x = y := by grind
            clear b7e13458
            have b7e13463 : (M.op x x) = (τ (σ x)) ∨ x = y := by
              first
              | (have i₁ := b7e15 (M.op x x)
                 have i₂ := b7e13459
                 grind)
              | exact superpose b7e13459 b7e15
              | exact resolve b7e15 b7e13459
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13459
            have b7e13493 : x = (M.op x x) ∨ x = y := by
              first
              | (have i₁ := b7e13463
                 have i₂ := b7e15 x
                 grind)
              | exact superpose b7e15 b7e13463
              | exact resolve b7e13463 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13463
            have b7e13494 : x = y := by
              first
              | (have r₁ := b7e13493
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e13493 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13493
            have b7e14354 : (σ x) ≠ (σ x) := by
              first
              | (have i₁ := b7e24
                 have i₂ := b7e13494
                 grind)
              | exact superpose b7e13494 b7e24
              | exact resolve b7e24 b7e13494
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13494
            have b7e14384 : False := by grind
            exact b7e14384
          · have b8e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : False := by grind
            exact b8e28
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = y := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e30 : False := by grind
          exact b9e30
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b10e23 : x = y := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e33 : (σ y) ≠ (σ (M.op y y)) := by grind
            have b10e56 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
            have b10e59 : (σ y) = (k (σ y) (σ y)) := by grind
            clear b10e56
            have b10e60 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b10e59
                 have i₂ := b10e20 y y
                 grind)
              | exact superpose b10e20 b10e59
              | exact resolve b10e59 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e59
            have b10e71 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
            clear b10e60
            have b10e72 : y = (M.op y y) := by
              first
              | (have r₁ := b10e71
                 have r₂ := b10e33
                 grind)
              | exact resolve b10e71 b10e33
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e33 b10e71
            have b10e75 : False := by grind
            exact b10e75
          · have b11e23 : x = y := by grind
            have b11e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e33 : False := by grind
            exact b11e33
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e22 : y ≠ (M.op y x) := by grind
            have b12e23 : x = y := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e33 : False := by grind
            exact b12e33
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = y := by grind
              have b13e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b13e970 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e66
              have b13e994 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
              clear b13e970
              have b13e997 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
              clear b13e994
              have b13e998 : y = (M.op y y) := by grind
              clear b13e997
              have b13e999 : False := by grind
              exact b13e999
            · have b14e24 : x = y := by grind
              have b14e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e36 : False := by grind
              exact b14e36
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e23 : x = y := by grind
            have b15e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e33 : False := by grind
            exact b15e33
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b16e24 : x = y := by grind
              have b16e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : False := by grind
              exact b16e36
            · have b17e24 : x = y := by grind
              have b17e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : False := by grind
              exact b17e36
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ y := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e13 (σ x) (σ y) X0
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e35 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 X1 X3
               have i₂ := b18e13 X2 X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e38 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e50 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
          have b18e51 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b18e16 x x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e16
            | (have r₁ := b18e16 x x
               have r₂ := b18e24
               grind)
            | exact resolve b18e16 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e52 : x = (k x x) := by grind
          clear b18e51
          have b18e53 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
          clear b18e50
          have b18e54 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b18e53
               have i₂ := b18e19 x y
               grind)
            | exact superpose b18e19 b18e53
            | exact resolve b18e53 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e53
          have b18e57 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b18e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e19 X0 X1
               have i₂ := b18e18 (σ X0) (σ X1)
               grind)
            | exact superpose b18e18 b18e19
            | (have j1 := b18e18 (σ X0) (σ X1)
               grind)
            | exact resolve b18e19 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e90 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ x) (σ x)
               have i₂ := b18e54
               grind)
            | exact superpose b18e54 b18e13
            | exact resolve b18e13 b18e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e92 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
            intro X0
            first
            | (have i₁ := b18e90 X0
               have i₂ := b18e38 X0
               grind)
            | exact superpose b18e38 b18e90
            | exact resolve b18e90 b18e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e90
          have b18e169 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b18e38 (σ x)
               have i₂ := b18e54
               grind)
            | exact superpose b18e54 b18e38
            | exact resolve b18e38 b18e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e38
          have b18e190 : (σ y) = (M.op (σ x) (σ (k x y))) := by
            first
            | (have i₁ := b18e169
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e169
            | exact resolve b18e169 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e169
          have b18e199 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (k x y)) X0)) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ (k x y)) (σ x)
               have i₂ := b18e190
               grind)
            | exact superpose b18e190 b18e13
            | exact resolve b18e13 b18e190
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e190
          have b18e202 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b18e199 X0
               have i₂ := b18e92 X0
               grind)
            | exact superpose b18e92 b18e199
            | exact resolve b18e199 b18e92
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e92 b18e199
          have b18e224 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b18e13 (σ x) (σ y) x
               have i₂ := b18e34 x
               grind)
            | exact superpose b18e34 b18e13
            | exact resolve b18e13 b18e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e34
          have b18e225 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e224
               have i₂ := b18e202 (σ x)
               grind)
            | exact superpose b18e202 b18e224
            | exact resolve b18e224 b18e202
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e202 b18e224
          have b18e232 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e225
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e225
            | exact resolve b18e225 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e225
          have b18e236 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b18e20
               have i₂ := b18e232
               grind)
            | exact superpose b18e232 b18e20
            | exact resolve b18e20 b18e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1124 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e57 x
               have i₂ := b18e54
               grind)
            | exact superpose b18e54 b18e57
            | exact resolve b18e57 b18e54
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e54 b18e57
          have b18e1154 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b18e1124
               have i₂ := b18e52
               grind)
            | exact superpose b18e52 b18e1124
            | exact resolve b18e1124 b18e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e52 b18e1124
          have b18e1155 : (σ x) = (σ (k x y)) := by grind
          clear b18e1154
          have b18e1178 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b18e14 (k x y)
               have i₂ := b18e1155
               grind)
            | exact superpose b18e1155 b18e14
            | exact resolve b18e14 b18e1155
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1155
          have b18e1179 : x = (k x y) := by
            first
            | (have i₁ := b18e1178
               have i₂ := b18e14 x
               grind)
            | exact superpose b18e14 b18e1178
            | exact resolve b18e1178 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1178
          have b18e1277 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e18 x y
               have i₂ := b18e1179
               grind)
            | exact superpose b18e1179 b18e18
            | (have j0 := b18e18 x y
               grind)
            | exact resolve b18e18 b18e1179
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1179
          have b18e1278 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b18e1277
               have r₂ := b18e22
               grind)
            | exact resolve b18e1277 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1277
          have b18e1280 : x = (M.op x y) := by
            first
            | (have r₁ := b18e1278
               have r₂ := b18e21
               grind)
            | exact resolve b18e1278 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1278
          have b18e1303 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e23
               have i₂ := b18e76 y x
               grind)
            | exact superpose b18e76 b18e23
            | (have j1 := b18e76 y x
               grind)
            | exact resolve b18e23 b18e76
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e76
          have b18e1362 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e1303
               have i₂ := b18e232
               grind)
            | exact superpose b18e232 b18e1303
            | exact resolve b18e1303 b18e232
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e232 b18e1303
          have b18e1363 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
          clear b18e1362
          have b18e1393 : (σ x) ≠ (σ y) := by
            first
            | (have i₁ := b18e236
               have i₂ := b18e1280
               grind)
            | exact superpose b18e1280 b18e236
            | exact resolve b18e236 b18e1280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e236
          have b18e1396 : x ≠ x ∨ (k y x) = (M.op y y) := by
            first
            | (have i₁ := b18e16 y x
               have i₂ := b18e1280
               grind)
            | exact superpose b18e1280 b18e16
            | (have j0 := b18e16 y x
               grind)
            | (have r₁ := b18e16 y x
               have r₂ := b18e1280
               grind)
            | exact resolve b18e16 b18e1280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1401 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e35 X0 y X1 x
               have i₂ := b18e1280
               grind)
            | exact superpose b18e1280 b18e35
            | exact resolve b18e35 b18e1280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e1407 : (k y x) = (M.op y y) := by grind
          clear b18e1396
          have b18e1619 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b18e14 (k y x)
               have i₂ := b18e1363
               grind)
            | exact superpose b18e1363 b18e14
            | exact resolve b18e14 b18e1363
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1363
          have b18e1638 : (k y x) = (τ (σ y)) := by
            first
            | (have r₁ := b18e1619
               have r₂ := b18e1393
               grind)
            | exact resolve b18e1619 b18e1393
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1393 b18e1619
          have b18e1648 : y = (k y x) := by
            first
            | (have i₁ := b18e1638
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e1638
            | exact resolve b18e1638 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1638
          have b18e1775 : y = (M.op y y) := by
            first
            | (have i₁ := b18e1648
               have i₂ := b18e1407
               grind)
            | exact superpose b18e1407 b18e1648
            | exact resolve b18e1648 b18e1407
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1407 b18e1648
          have b18e1888 : ∀ X0 X1 : G, (M.op y X1) = (M.op (M.op X0 y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e35 X0 y X1 y
               have i₂ := b18e1775
               grind)
            | exact superpose b18e1775 b18e35
            | exact resolve b18e35 b18e1775
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e35
          have b18e1897 : ∀ X1 : G, (M.op x X1) = (M.op y X1) := by
            intro X1
            first
            | (have i₁ := b18e1888 x X1
               have i₂ := b18e1401 x X1
               grind)
            | exact superpose b18e1401 b18e1888
            | exact resolve b18e1888 b18e1401
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1401 b18e1888
          have b18e2272 : y = (M.op x y) := by
            first
            | (have i₁ := b18e1775
               have i₂ := b18e1897 y
               grind)
            | exact superpose b18e1897 b18e1775
            | exact resolve b18e1775 b18e1897
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1775 b18e1897
          have b18e2273 : x = y := by
            first
            | (have i₁ := b18e2272
               have i₂ := b18e1280
               grind)
            | exact superpose b18e1280 b18e2272
            | exact resolve b18e2272 b18e1280
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e1280 b18e2272
          have b18e2288 : False := by grind
          exact b18e2288
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b19e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ y := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b19e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b19e34 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
              intro X0
              first
              | (have i₁ := b19e14 (σ x) (σ y) X0
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e38 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 (σ x) (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e49 : (σ y) ≠ (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
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
            have b19e52 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
            clear b19e49
            have b19e53 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
              first
              | (have i₁ := b19e52
                 have i₂ := b19e20 x y
                 grind)
              | exact superpose b19e20 b19e52
              | exact resolve b19e52 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e52
            have b19e54 : (σ x) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ x) (σ x)) := by
              first
              | (have i₁ := b19e17 (σ x) (σ x)
                 have i₂ := b19e53
                 grind)
              | exact superpose b19e53 b19e17
              | exact resolve b19e17 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e55 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ (k x y)) X0) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 (σ x) (σ x)
                 have i₂ := b19e53
                 grind)
              | exact superpose b19e53 b19e14
              | exact resolve b19e14 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e57 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ (k x y)) X0) := by
              intro X0
              first
              | (have i₁ := b19e55 X0
                 have i₂ := b19e38 X0
                 grind)
              | exact superpose b19e38 b19e55
              | exact resolve b19e55 b19e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e55
            have b19e58 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b19e54
                 have i₂ := b19e20 x x
                 grind)
              | exact superpose b19e20 b19e54
              | exact resolve b19e54 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e54
            have b19e60 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b19e76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X0 X1
                 have i₂ := b19e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b19e19 b19e20
              | (have j1 := b19e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b19e20 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e141 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ (k x y))) := by
              first
              | (have i₁ := b19e38 (σ x)
                 have i₂ := b19e53
                 grind)
              | exact superpose b19e53 b19e38
              | exact resolve b19e38 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e38
            have b19e157 : (σ y) = (M.op (σ x) (σ (k x y))) := by
              first
              | (have i₁ := b19e141
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e141
              | exact resolve b19e141 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e141
            have b19e165 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (k x y)) X0)) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 (σ (k x y)) (σ x)
                 have i₂ := b19e157
                 grind)
              | exact superpose b19e157 b19e14
              | exact resolve b19e14 b19e157
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e157
            have b19e168 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := b19e165 X0
                 have i₂ := b19e57 X0
                 grind)
              | exact superpose b19e57 b19e165
              | exact resolve b19e165 b19e57
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e57 b19e165
            have b19e189 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
              first
              | (have i₁ := b19e14 (σ x) (σ y) x
                 have i₂ := b19e34 x
                 grind)
              | exact superpose b19e34 b19e14
              | exact resolve b19e14 b19e34
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e34
            have b19e190 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b19e189
                 have i₂ := b19e168 (σ x)
                 grind)
              | exact superpose b19e168 b19e189
              | exact resolve b19e189 b19e168
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e168 b19e189
            have b19e197 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b19e190
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e190
              | exact resolve b19e190 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e190
            have b19e1024 : (σ (k x y)) = (σ (k x x)) ∨ (σ x) = (σ (k x y)) := by
              first
              | (have i₁ := b19e60 x
                 have i₂ := b19e53
                 grind)
              | exact superpose b19e53 b19e60
              | exact resolve b19e60 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e53 b19e60
            have b19e1055 : (σ (k x y)) = (σ (k x x)) := by
              first
              | (have r₁ := b19e1024
                 have r₂ := b19e58
                 grind)
              | exact resolve b19e1024 b19e58
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e58 b19e1024
            have b19e1074 : (k x y) = (τ (σ (k x x))) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e1055
                 grind)
              | exact superpose b19e1055 b19e15
              | exact resolve b19e15 b19e1055
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1055
            have b19e1075 : (k x y) = (k x x) := by
              first
              | (have i₁ := b19e1074
                 have i₂ := b19e15 (k x x)
                 grind)
              | exact superpose b19e15 b19e1074
              | exact resolve b19e1074 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1074
            have b19e1148 : (M.op x y) = (k x x) ∨ x = y ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e19 x y
                 have i₂ := b19e1075
                 grind)
              | exact superpose b19e1075 b19e19
              | (have j0 := b19e19 x y
                 grind)
              | exact resolve b19e19 b19e1075
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1075
            have b19e1149 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b19e1148
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e1148 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1148
            have b19e1151 : (M.op x y) = (k x x) := by
              first
              | (have r₁ := b19e1149
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e1149 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1149
            have b19e1174 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e24
                 have i₂ := b19e76 y x
                 grind)
              | exact superpose b19e76 b19e24
              | (have j1 := b19e76 y x
                 grind)
              | exact resolve b19e24 b19e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e76
            have b19e1231 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e1174
                 have i₂ := b19e197
                 grind)
              | exact superpose b19e197 b19e1174
              | exact resolve b19e1174 b19e197
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e197 b19e1174
            have b19e1232 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) := by grind
            clear b19e1231
            have b19e1288 : (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
            clear b19e1151
            have b19e1289 : (M.op x y) = (M.op x x) := by
              first
              | (have r₁ := b19e1288
                 have r₂ := b19e25
                 grind)
              | exact resolve b19e1288 b19e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1288
            have b19e1383 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e15 (k y x)
                 have i₂ := b19e1232
                 grind)
              | exact superpose b19e1232 b19e15
              | exact resolve b19e15 b19e1232
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1232
            have b19e1397 : y = (k y x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e1383
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e1383
              | exact resolve b19e1383 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1383
            have b19e2038 : y = (M.op y x) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e19 y x
                 have i₂ := b19e1397
                 grind)
              | exact superpose b19e1397 b19e19
              | (have j0 := b19e19 x y
                 grind)
              | exact resolve b19e19 b19e1397
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1397
            have b19e2039 : x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b19e2038
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e2038 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2038
            have b19e2041 : x = (M.op x y) ∨ (σ x) = (σ y) := by
              first
              | (have r₁ := b19e2039
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e2039 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2039
            have b19e2043 : x = (M.op x x) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b19e2041
                 have i₂ := b19e1289
                 grind)
              | exact superpose b19e1289 b19e2041
              | exact resolve b19e2041 b19e1289
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1289 b19e2041
            have b19e2045 : (σ x) = (σ y) := by
              first
              | (have r₁ := b19e2043
                 have r₂ := b19e25
                 grind)
              | exact resolve b19e2043 b19e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2043
            have b19e2259 : y = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 y
                 have i₂ := b19e2045
                 grind)
              | exact superpose b19e2045 b19e15
              | exact resolve b19e15 b19e2045
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2045
            have b19e2274 : x = y := by
              first
              | (have i₁ := b19e2259
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e2259
              | exact resolve b19e2259 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2259
            have b19e2279 : False := by grind
            exact b19e2279
          · have b20e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : False := by grind
            exact b20e28
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e23 : x ≠ y := by grind
            have b21e25 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 y
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e15
              | exact resolve b21e15 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e31 : x = y := by
              first
              | (have i₁ := b21e30
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e30
              | exact resolve b21e30 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30
            have b21e32 : False := by grind
            exact b21e32
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e24 : x ≠ y := by grind
              have b22e26 : (σ x) = (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e32 : y = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 y
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e16
                | exact resolve b22e16 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e33 : x = y := by
                first
                | (have i₁ := b22e32
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e32
                | exact resolve b22e32 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e32
              have b22e34 : False := by grind
              exact b22e34
            · have b23e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : False := by grind
              exact b23e30
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op y x) := by grind
            have b24e23 : x ≠ y := by grind
            have b24e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
            have b24e1424 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b24e24
                 have i₂ := b24e67 x y
                 grind)
              | exact superpose b24e67 b24e24
              | (have j1 := b24e67 x y
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e67 x y
                 grind)
              | exact resolve b24e24 b24e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e67
            have b24e1446 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b24e1424
            have b24e1451 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b24e1446
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e1446 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1446
            have b24e1460 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1451
                 grind)
              | exact superpose b24e1451 b24e21
              | exact resolve b24e21 b24e1451
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1451
            have b24e1730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e1460
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1460
              | (have j1 := b24e19 x y
                 grind)
              | (have r₁ := b24e1460
                 have r₂ := b24e19 (σ (M.op x y)) (σ (k x y))
                 grind)
              | (have r₁ := b24e1460
                 have r₂ := b24e19 (σ (k x y)) (σ (M.op x y))
                 grind)
              | exact resolve b24e1460 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1460
            have b24e1731 : x = y ∨ y = (M.op y x) := by grind
            clear b24e1730
            have b24e1732 : y = (M.op y x) := by
              first
              | (have r₁ := b24e1731
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1731 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1731
            have b24e1733 : False := by grind
            exact b24e1733
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op y x) := by grind
              have b25e24 : x ≠ y := by grind
              have b25e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b25e1883 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e25
                   have i₂ := b25e68 x y
                   grind)
                | exact superpose b25e68 b25e25
                | (have j1 := b25e68 x y
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e68 x y
                   grind)
                | exact resolve b25e25 b25e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e68
              have b25e1915 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
              clear b25e1883
              have b25e1922 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have r₁ := b25e1915
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e1915 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1915
              have b25e1933 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e1922
                   grind)
                | exact superpose b25e1922 b25e22
                | exact resolve b25e22 b25e1922
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1922
              have b25e1962 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e1933
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e1933
                | (have j1 := b25e20 x y
                   grind)
                | (have r₁ := b25e1933
                   have r₂ := b25e20 (σ (M.op x y)) (σ (k x y))
                   grind)
                | (have r₁ := b25e1933
                   have r₂ := b25e20 (σ (k x y)) (σ (M.op x y))
                   grind)
                | exact resolve b25e1933 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1933
              have b25e1963 : x = y ∨ y = (M.op y x) := by grind
              clear b25e1962
              have b25e1964 : y = (M.op y x) := by
                first
                | (have r₁ := b25e1963
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e1963 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1963
              have b25e1965 : False := by grind
              exact b25e1965
            · have b26e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : False := by grind
              exact b26e30

/-- `Equation4456`: `x ◇ (y ◇ x) = (z ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_x_pxx_pxy_Equation4456 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4456 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4456.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
      · have b0e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
          intro X0 X1 X2
          grind
        have b0e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b0e20 : y = (M.op y x) := by grind
        have b0e21 : (σ y) = (M.op (σ y) (σ x)) := by grind
        have b0e22 : x = (M.op x x) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a
        have b0e44 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e12 X0 x y
             have i₂ := b0e20
             grind)
          | exact superpose b0e20 b0e12
          | exact resolve b0e12 b0e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e45 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
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
        have b0e48 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
          intro X0
          first
          | (have i₁ := b0e44 X0
             have i₂ := b0e45 X0
             grind)
          | exact superpose b0e45 b0e44
          | exact resolve b0e44 b0e45
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e44 b0e45
        have b0e53 : y = (M.op x x) := by
          first
          | (have i₁ := b0e20
             have i₂ := b0e48 x
             grind)
          | exact superpose b0e48 b0e20
          | exact resolve b0e20 b0e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e48
        have b0e54 : x = y := by
          first
          | (have i₁ := b0e53
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e53
          | exact resolve b0e53 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e53
        have b0e66 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e19
             have i₂ := b0e54
             grind)
          | exact superpose b0e54 b0e19
          | exact resolve b0e19 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b0e68 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b0e21
             have i₂ := b0e54
             grind)
          | exact superpose b0e54 b0e21
          | exact resolve b0e21 b0e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e54
        have b0e70 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b0e66
             have i₂ := b0e68
             grind)
          | exact superpose b0e68 b0e66
          | exact resolve b0e66 b0e68
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e66 b0e68
        have b0e71 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b0e70
             have i₂ := b0e22
             grind)
          | exact superpose b0e22 b0e70
          | exact resolve b0e70 b0e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b0e70
        have b0e72 : False := by grind
        exact b0e72
      · rcases eq_or_ne (x) (x) with h2b | h2b
        · have b1e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b1e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b1e21 : y = (M.op y x) := by grind
          have b1e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b1e35 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b1e13 (σ x) (σ y) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e13
            | exact resolve b1e13 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e36 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X2 X1 X3
               have i₂ := b1e13 X2 X1 X0
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e37 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b1e13 X3 (M.op X1 X2) X2
               have i₂ := b1e13 X2 X1 X0
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e38 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X2 X0 (M.op x X1)
               have i₂ := b1e13 X0 X1 x
               grind)
            | exact superpose b1e13 b1e13
            | exact resolve b1e13 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e40 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 x y
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e13
            | exact resolve b1e13 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e43 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
            first
            | (have i₁ := b1e40 (M.op x x)
               have i₂ := b1e40 x
               grind)
            | exact superpose b1e40 b1e40
            | exact resolve b1e40 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e45 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X0 x X1
               have i₂ := b1e40 X0
               grind)
            | exact superpose b1e40 b1e13
            | exact resolve b1e13 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e46 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e13 X1 (M.op x X0) X0
               have i₂ := b1e40 X0
               grind)
            | exact superpose b1e40 b1e13
            | exact resolve b1e13 b1e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e40
          have b1e49 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
            first
            | (have i₁ := b1e43
               have i₂ := b1e45 (M.op y x) x
               grind)
            | exact superpose b1e45 b1e43
            | exact resolve b1e43 b1e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e43
          have b1e50 : (M.op y (M.op x x)) = (M.op y y) := by
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
          have b1e68 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 (M.op x x) y
               have i₂ := b1e50
               grind)
            | exact superpose b1e50 b1e13
            | exact resolve b1e13 b1e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e50
          have b1e72 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e68 X0
               have i₂ := b1e46 x X0
               grind)
            | exact superpose b1e46 b1e68
            | exact resolve b1e68 b1e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e46 b1e68
          have b1e74 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
            intro X0
            first
            | (have i₁ := b1e72 X0
               have i₂ := b1e45 X0 y
               grind)
            | exact superpose b1e45 b1e72
            | exact resolve b1e72 b1e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e45 b1e72
          have b1e88 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b1e13 X0 y y
               have i₂ := b1e74 X0
               grind)
            | exact superpose b1e74 b1e13
            | exact resolve b1e13 b1e74
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e74
          have b1e104 : y = (M.op x y) := by
            first
            | (have i₁ := b1e88 x
               have i₂ := b1e21
               grind)
            | exact superpose b1e21 b1e88
            | exact resolve b1e88 b1e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e88
          have b1e152 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b1e36 X0 (σ x) X1 (σ y)
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e36
            | exact resolve b1e36 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e36
          have b1e337 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b1e13 X0 (M.op X2 X1) X1
               have i₂ := b1e38 X1 X2 X0
               grind)
            | exact superpose b1e38 b1e13
            | exact resolve b1e13 b1e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e38
          have b1e614 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b1e37 X1 (σ y) (σ x) X0
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e37
            | exact resolve b1e37 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b1e727 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b1e35 (M.op (M.op x X0) X1)
               have i₂ := b1e37 x X0 X1 (σ y)
               grind)
            | exact superpose b1e37 b1e35
            | exact resolve b1e35 b1e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e35 b1e37
          have b1e730 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b1e727 X0 X1
               have i₂ := b1e13 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
               grind)
            | exact superpose b1e13 b1e727
            | exact resolve b1e727 b1e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e727
          have b1e774 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b1e614 X0 x
               have i₂ := b1e152 (M.op x (σ y)) X0
               grind)
            | exact superpose b1e152 b1e614
            | exact resolve b1e614 b1e152
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e152 b1e614
          have b1e780 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b1e730 x x
               have i₂ := b1e337 (σ x) (σ y) (M.op x x)
               grind)
            | exact superpose b1e337 b1e730
            | exact resolve b1e730 b1e337
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e337 b1e730
          have b1e798 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b1e780
               have i₂ := b1e774 (σ x)
               grind)
            | exact superpose b1e774 b1e780
            | exact resolve b1e780 b1e774
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e774 b1e780
          have b1e804 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b1e798
               have i₂ := b1e22
               grind)
            | exact superpose b1e22 b1e798
            | exact resolve b1e798 b1e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e798
          have b1e805 : (σ (M.op x y)) ≠ (σ y) := by
            first
            | (have i₁ := b1e20
               have i₂ := b1e804
               grind)
            | exact superpose b1e804 b1e20
            | exact resolve b1e20 b1e804
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e804
          have b1e819 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b1e805
               have i₂ := b1e104
               grind)
            | exact superpose b1e104 b1e805
            | exact resolve b1e805 b1e104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b1e104 b1e805
          have b1e820 : False := by grind
          exact b1e820
        · have b2e24 : x ≠ x := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h2a h2b
          have b2e26 : False := by grind
          exact b2e26
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b3e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b3e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b3e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b3e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b3e22 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b3e23 : (σ x) = (σ y) := by grind
          have b3e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b3e26 : (σ x) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e22
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e22
            | exact resolve b3e22 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e27 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e20
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e20
            | exact resolve b3e20 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e28 : y = (τ (σ x)) := by
            first
            | (have i₁ := b3e14 y
               have i₂ := b3e23
               grind)
            | exact superpose b3e23 b3e14
            | exact resolve b3e14 b3e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e29 : x = y := by
            first
            | (have i₁ := b3e28
               have i₂ := b3e14 x
               grind)
            | exact superpose b3e14 b3e28
            | exact resolve b3e28 b3e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e28
          have b3e32 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b3e16 x x
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e16
            | (have j0 := b3e16 x x
               grind)
            | (have r₁ := b3e16 x x
               have r₂ := b3e24
               grind)
            | exact resolve b3e16 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b3e33 : x = (k x x) := by grind
          clear b3e32
          have b3e63 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b3e1293 : (σ (M.op x y)) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b3e27
               have i₂ := b3e63 x
               grind)
            | exact superpose b3e63 b3e27
            | (have j1 := b3e63 x
               grind)
            | exact resolve b3e27 b3e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e27 b3e63
          have b3e1315 : (σ (M.op x y)) ≠ (σ (k x x)) := by
            first
            | (have r₁ := b3e1293
               have r₂ := b3e26
               grind)
            | exact resolve b3e1293 b3e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e26 b3e1293
          have b3e1319 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b3e1315
               have i₂ := b3e33
               grind)
            | exact superpose b3e33 b3e1315
            | exact resolve b3e1315 b3e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e33 b3e1315
          have b3e1322 : (σ x) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b3e1319
               have i₂ := b3e29
               grind)
            | exact superpose b3e29 b3e1319
            | exact resolve b3e1319 b3e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e29 b3e1319
          have b3e1324 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b3e1322
               have i₂ := b3e24
               grind)
            | exact superpose b3e24 b3e1322
            | exact resolve b3e1322 b3e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b3e1322
          have b3e1325 : False := by grind
          exact b3e1325
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b4e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b4e22 : y = (M.op y x) := by grind
            have b4e24 : (σ x) = (σ y) := by grind
            have b4e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b4e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b4e15 y
                 have i₂ := b4e24
                 grind)
              | exact superpose b4e24 b4e15
              | exact resolve b4e15 b4e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b4e31 : x = y := by
              first
              | (have i₁ := b4e30
                 have i₂ := b4e15 x
                 grind)
              | exact superpose b4e15 b4e30
              | exact resolve b4e30 b4e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e30
            have b4e32 : x = (M.op x x) := by
              first
              | (have i₁ := b4e22
                 have i₂ := b4e31
                 grind)
              | exact superpose b4e31 b4e22
              | exact resolve b4e22 b4e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b4e31
            have b4e33 : False := by grind
            exact b4e33
          · have b5e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b5e28 : False := by grind
            exact b5e28
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b6e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b6e21 : y = (M.op y x) := by grind
          have b6e23 : (σ x) ≠ (σ y) := by grind
          have b6e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a
          have b6e35 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x y
               have i₂ := b6e21
               grind)
            | exact superpose b6e21 b6e13
            | exact resolve b6e13 b6e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e36 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x X0)) := by
            intro X0
            first
            | (have i₁ := b6e13 X0 x x
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e13
            | exact resolve b6e13 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b6e41 : ∀ X0 : G, (M.op x X0) = (M.op y X0) := by
            intro X0
            first
            | (have i₁ := b6e35 X0
               have i₂ := b6e36 X0
               grind)
            | exact superpose b6e36 b6e35
            | exact resolve b6e35 b6e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e35 b6e36
          have b6e46 : y = (M.op x x) := by
            first
            | (have i₁ := b6e21
               have i₂ := b6e41 x
               grind)
            | exact superpose b6e41 b6e21
            | exact resolve b6e21 b6e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e41
          have b6e47 : x = y := by
            first
            | (have i₁ := b6e46
               have i₂ := b6e24
               grind)
            | exact superpose b6e24 b6e46
            | exact resolve b6e46 b6e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e46
          have b6e60 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b6e23
               have i₂ := b6e47
               grind)
            | exact superpose b6e47 b6e23
            | exact resolve b6e23 b6e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b6e47
          have b6e62 : False := by grind
          exact b6e62
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b7e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b7e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b7e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b7e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b7e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b7e22 : y = (M.op y x) := by grind
            have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b7e24 : (σ x) ≠ (σ y) := by grind
            have b7e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b7e28 : y ≠ y ∨ x = (k x y) := by
              first
              | (have i₁ := b7e17 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e17
              | (have j0 := b7e17 x y
                 grind)
              | (have r₁ := b7e17 x y
                 have r₂ := b7e22
                 grind)
              | exact resolve b7e17 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e29 : x = (k x y) := by grind
            clear b7e28
            have b7e30 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 (τ X0) X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e31 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X1 (τ X0)
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e20
              | exact resolve b7e20 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e35 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k (τ X0) X1)
                 have i₂ := b7e30 X0 X1
                 grind)
              | exact superpose b7e30 b7e15
              | exact resolve b7e15 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e37 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X0 (M.op X2 X1) X3
                 have i₂ := b7e14 X0 X1 X2
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X2 X1 X3
                 have i₂ := b7e14 X2 X1 X0
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e39 : ∀ X0 : G, (M.op X0 (M.op x X0)) = (M.op y X0) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 x y
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e14
              | exact resolve b7e14 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e40 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e14 X3 (M.op X1 X2) X2
                 have i₂ := b7e14 X2 X1 X0
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e41 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e14 X2 X0 (M.op x X1)
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e14
              | exact resolve b7e14 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e44 : (M.op y (M.op x x)) = (M.op (M.op x x) (M.op y x)) := by
              first
              | (have i₁ := b7e39 (M.op x x)
                 have i₂ := b7e39 x
                 grind)
              | exact superpose b7e39 b7e39
              | exact resolve b7e39 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e46 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 x) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 x X1
                 have i₂ := b7e39 X0
                 grind)
              | exact superpose b7e39 b7e14
              | exact resolve b7e14 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e47 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x X0) X1)) = (M.op (M.op y X0) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (M.op x X0) X0
                 have i₂ := b7e39 X0
                 grind)
              | exact superpose b7e39 b7e14
              | exact resolve b7e14 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e48 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op x X0)) = (M.op (M.op x X0) (M.op y X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 (M.op x X0) X0 X1
                 have i₂ := b7e39 X0
                 grind)
              | exact superpose b7e39 b7e14
              | exact resolve b7e14 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e50 : (M.op y (M.op x x)) = (M.op y (M.op y x)) := by
              first
              | (have i₁ := b7e44
                 have i₂ := b7e46 (M.op y x) x
                 grind)
              | exact superpose b7e46 b7e44
              | exact resolve b7e44 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e44
            have b7e51 : (M.op y (M.op x x)) = (M.op y y) := by
              first
              | (have i₁ := b7e50
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e50
              | exact resolve b7e50 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e50
            have b7e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b7e54 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              grind
            have b7e55 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              first
              | (have i₁ := b7e54 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e54
              | (have j0 := b7e54 X0
                 grind)
              | exact resolve b7e54 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e54
            have b7e63 : ∀ X0 X1 : G, (M.op y X0) ≠ (M.op X1 x) ∨ (k X0 (M.op X1 x)) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e17 X0 (M.op X1 x)
                 have i₂ := b7e46 X0 X1
                 grind)
              | exact superpose b7e46 b7e17
              | (have j0 := b7e17 X0 (M.op X1 x)
                 grind)
              | (have r₁ := b7e17 x (M.op y x)
                 have r₂ := b7e46 x y
                 grind)
              | exact resolve b7e17 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e20 X0 X1
                 have i₂ := b7e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b7e19 b7e20
              | (have j1 := b7e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b7e20 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e70 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 (τ X0)) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e30 X0 X1
                 have i₂ := b7e19 (τ X0) X1
                 grind)
              | exact superpose b7e19 b7e30
              | (have j1 := b7e19 (τ X0) X1
                 grind)
              | exact resolve b7e30 b7e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e72 : ∀ X0 : G, (M.op X0 (M.op (M.op x x) X0)) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 (M.op x x) y
                 have i₂ := b7e51
                 grind)
              | exact superpose b7e51 b7e14
              | exact resolve b7e14 b7e51
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e51
            have b7e76 : ∀ X0 : G, (M.op (M.op y x) X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e72 X0
                 have i₂ := b7e47 x X0
                 grind)
              | exact superpose b7e47 b7e72
              | exact resolve b7e72 b7e47
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e47 b7e72
            have b7e78 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
              intro X0
              first
              | (have i₁ := b7e76 X0
                 have i₂ := b7e46 X0 y
                 grind)
              | exact superpose b7e46 b7e76
              | exact resolve b7e76 b7e46
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e76
            have b7e86 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b7e15 (k X0 (τ X1))
                 have i₂ := b7e31 X1 X0
                 grind)
              | exact superpose b7e31 b7e15
              | exact resolve b7e15 b7e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e31
            have b7e96 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op y X0)) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 y y
                 have i₂ := b7e78 X0
                 grind)
              | exact superpose b7e78 b7e14
              | exact resolve b7e14 b7e78
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e78
            have b7e123 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e38 X2 X0 X3 (M.op x X1)
                 have i₂ := b7e14 X0 X1 x
                 grind)
              | exact superpose b7e14 b7e38
              | exact resolve b7e38 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e146 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b7e17 X2 (M.op X3 X1)
                 have i₂ := b7e38 X3 X1 X2 X0
                 grind)
              | (have i₁ := b7e17 X2 (M.op X3 X1)
                 have i₂ := b7e38 X0 X1 X2 X3
                 grind)
              | exact superpose b7e38 b7e17
              | (have j0 := b7e17 X2 (M.op X3 X1)
                 grind)
              | (have r₁ := b7e17 X2 (M.op (M.op X3 X2) X2)
                 have r₂ := b7e38 (M.op X3 X2) X2 X2 X3
                 grind)
              | (have r₁ := b7e17 X2 (M.op (M.op X0 X2) X2)
                 have r₂ := b7e38 X0 X2 X2 (M.op X0 X2)
                 grind)
              | exact resolve b7e17 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e149 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x (M.op X2 X1))) = (M.op y (M.op X2 X1)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e39 (M.op X2 X1)
                 have i₂ := b7e38 X2 X1 (M.op x (M.op X2 X1)) X0
                 grind)
              | (have i₁ := b7e39 (M.op X2 X1)
                 have i₂ := b7e38 X0 X1 (M.op x (M.op X2 X1)) X2
                 grind)
              | exact superpose b7e38 b7e39
              | exact resolve b7e39 b7e38
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e321 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e41 X1 x X0
                 have i₂ := b7e37 X0 X1 x X1
                 grind)
              | exact superpose b7e37 b7e41
              | exact resolve b7e41 b7e37
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e41
            have b7e682 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            clear b7e35
            have b7e687 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b7e682 X0
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e682
              | (have j0 := b7e682 X0
                 grind)
              | exact resolve b7e682 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e682
            have b7e1013 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 (σ X0) (σ X0) X1
                 have i₂ := b7e53 X0
                 grind)
              | exact superpose b7e53 b7e14
              | (have j1 := b7e53 X0
                 grind)
              | exact resolve b7e14 b7e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1014 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X1 (σ X0) (σ X0)
                 have i₂ := b7e53 X0
                 grind)
              | exact superpose b7e53 b7e14
              | (have j1 := b7e53 X0
                 grind)
              | exact resolve b7e14 b7e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1029 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b7e53 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1169 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b7e23
                 have i₂ := b7e69 x y
                 grind)
              | exact superpose b7e69 b7e23
              | (have j1 := b7e69 x y
                 grind)
              | (have r₁ := b7e23
                 have r₂ := b7e69 x y
                 grind)
              | exact resolve b7e23 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1172 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e17 (σ X1) (σ X0)
                 have i₂ := b7e69 X1 X0
                 grind)
              | exact superpose b7e69 b7e17
              | (have j0 := b7e17 (σ X1) (σ X0)
                 have j1 := b7e69 X1 X0
                 grind)
              | (have r₁ := b7e17 (σ X0) (σ X1)
                 have r₂ := b7e69 X0 X1
                 grind)
              | exact resolve b7e17 b7e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e69
            have b7e1188 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have j0 := b7e1172 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1172
            have b7e1189 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b7e1169
            have b7e1193 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e1188 X0 X1
                 have i₂ := b7e20 X1 X0
                 grind)
              | exact superpose b7e20 b7e1188
              | (have j0 := b7e1188 X0 X1
                 grind)
              | exact resolve b7e1188 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1188
            have b7e1194 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b7e1189
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e1189 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1189
            have b7e1202 : (σ x) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b7e1194
                 have i₂ := b7e29
                 grind)
              | exact superpose b7e29 b7e1194
              | exact resolve b7e1194 b7e29
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e29 b7e1194
            have b7e1204 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (M.op X0 (σ x)) (σ y)) := by
              intro X0
              first
              | (have i₁ := b7e14 (σ y) (σ x) X0
                 have i₂ := b7e1202
                 grind)
              | exact superpose b7e1202 b7e14
              | exact resolve b7e14 b7e1202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1205 : ∀ X0 : G, (M.op X0 (M.op (σ y) X0)) = (M.op (σ x) X0) := by
              intro X0
              first
              | (have i₁ := b7e14 X0 (σ y) (σ x)
                 have i₂ := b7e1202
                 grind)
              | exact superpose b7e1202 b7e14
              | exact resolve b7e14 b7e1202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e1210 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op (σ y) X1))) = (M.op (M.op X0 (σ x)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e37 X1 (σ y) (σ x) X0
                 have i₂ := b7e1202
                 grind)
              | exact superpose b7e1202 b7e37
              | exact resolve b7e37 b7e1202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e37
            have b7e1212 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ y)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e38 X0 (σ y) X1 (σ x)
                 have i₂ := b7e1202
                 grind)
              | exact superpose b7e1202 b7e38
              | exact resolve b7e38 b7e1202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e38
            have b7e1219 : ∀ X0 X1 : G, (M.op X1 (M.op (σ y) X1)) = (M.op (M.op X0 (σ x)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e1210 X0 X1
                 have i₂ := b7e321 X1 (σ y)
                 grind)
              | exact superpose b7e321 b7e1210
              | exact resolve b7e1210 b7e321
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e321 b7e1210
            have b7e1224 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (M.op X0 (σ x)) X1) := by
              intro X0 X1
              first
              | (have i₁ := b7e1219 X0 X1
                 have i₂ := b7e1205 X1
                 grind)
              | exact superpose b7e1205 b7e1219
              | exact resolve b7e1219 b7e1205
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1205 b7e1219
            have b7e2233 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (M.op X2 X1) (σ y)) X0) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e40 X2 X1 (σ y) X0
                 have i₂ := b7e1212 X1 X0
                 grind)
              | exact superpose b7e1212 b7e40
              | exact resolve b7e40 b7e1212
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e40
            have b7e2265 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (σ x) X0)) := by
              intro X0
              first
              | (have i₁ := b7e2233 X0 x x
                 have i₂ := b7e1212 (M.op x x) X0
                 grind)
              | exact superpose b7e1212 b7e2233
              | exact resolve b7e2233 b7e1212
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1212 b7e2233
            have b7e4447 : (σ x) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b7e2265 (σ y)
                 have i₂ := b7e1202
                 grind)
              | exact superpose b7e1202 b7e2265
              | exact resolve b7e2265 b7e1202
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1202 b7e2265
            have b7e10414 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b7e1029 (τ X0)
                 have i₂ := b7e30 X0 (τ X0)
                 grind)
              | exact superpose b7e30 b7e1029
              | (have j0 := b7e1029 (τ X0)
                 grind)
              | exact resolve b7e1029 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1029
            have b7e10417 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b7e10414 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e10414
              | (have j0 := b7e10414 X0
                 grind)
              | exact resolve b7e10414 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e10414
            have b7e10422 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e10417 X0
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e10417
              | (have j0 := b7e10417 X0
                 grind)
              | exact resolve b7e10417 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e10417
            have b7e10472 : (M.op (σ y) (σ x)) = (M.op (σ (k x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e1204 (σ x)
                 have i₂ := b7e53 x
                 grind)
              | exact superpose b7e53 b7e1204
              | (have j1 := b7e53 x
                 grind)
              | exact resolve b7e1204 b7e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1204
            have b7e10594 : (σ x) = (M.op (σ (k x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e10472
                 have i₂ := b7e4447
                 grind)
              | exact superpose b7e4447 b7e10472
              | exact resolve b7e10472 b7e4447
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e4447 b7e10472
            have b7e10870 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
              intro X0 X1
              first
              | (have j0 := b7e146 X0 X0 X0 (M.op X1 X0)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e146
            have b7e10954 : (σ x) = (k (σ x) (M.op (σ x) (σ x))) := by
              first
              | (have i₁ := b7e10870 (σ x) x
                 have i₂ := b7e1224 x (σ x)
                 grind)
              | exact superpose b7e1224 b7e10870
              | exact resolve b7e10870 b7e1224
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1224
            have b7e10964 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) (M.op (M.op X0 X1) (M.op X2 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b7e10870 (M.op X2 X1) X1
                 have i₂ := b7e123 X1 X2 X0 (M.op X2 X1)
                 grind)
              | exact superpose b7e123 b7e10870
              | exact resolve b7e10870 b7e123
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e123
            have b7e13800 : (k x (τ (M.op (σ x) (σ x)))) = (τ (σ x)) := by
              first
              | (have i₁ := b7e86 x (M.op (σ x) (σ x))
                 have i₂ := b7e10954
                 grind)
              | exact superpose b7e10954 b7e86
              | exact resolve b7e86 b7e10954
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e86 b7e10954
            have b7e13802 : x = (k x (τ (M.op (σ x) (σ x)))) := by
              first
              | (have i₁ := b7e13800
                 have i₂ := b7e15 x
                 grind)
              | exact superpose b7e15 b7e13800
              | exact resolve b7e13800 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13800
            have b7e15440 : x = (k x (τ (σ (k x x)))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e13802
                 have i₂ := b7e53 x
                 grind)
              | exact superpose b7e53 b7e13802
              | (have j1 := b7e53 x
                 grind)
              | exact resolve b7e13802 b7e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e53
            have b7e15444 : x = (k x (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e15440
                 have i₂ := b7e15 (k x x)
                 grind)
              | exact superpose b7e15 b7e15440
              | exact resolve b7e15440 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e15440
            have b7e23892 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e55 (σ X0)
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e55
              | exact resolve b7e55 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e55
            have b7e23914 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e23892 X0
                 have i₂ := b7e20 X0 X0
                 grind)
              | exact superpose b7e20 b7e23892
              | (have j0 := b7e23892 X0
                 grind)
              | exact resolve b7e23892 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e23892
            have b7e53963 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e70 (σ X0) X1
                 have i₂ := b7e15 X0
                 grind)
              | exact superpose b7e15 b7e70
              | exact resolve b7e70 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e70
            have b7e54030 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e53963 X0 X1
                 have i₂ := b7e20 X0 X1
                 grind)
              | exact superpose b7e20 b7e53963
              | (have j0 := b7e53963 X0 X1
                 grind)
              | exact resolve b7e53963 b7e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e53963
            have b7e55764 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ x = (k x (M.op X0 x)) := by
              intro X0
              first
              | (have i₁ := b7e63 x X0
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e63
              | (have j0 := b7e63 x X0
                 grind)
              | exact resolve b7e63 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e63
            have b7e89028 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (τ X0)) X1)) = (M.op (k X0 (σ (τ X0))) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e1014 (τ X0) X1
                 have i₂ := b7e30 X0 (τ X0)
                 grind)
              | exact superpose b7e30 b7e1014
              | (have j0 := b7e1014 (τ X0) X1
                 grind)
              | exact resolve b7e1014 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1014
            have b7e89677 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e89028 X0 X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e89028
              | (have j0 := b7e89028 X0 X1
                 grind)
              | exact resolve b7e89028 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e89028
            have b7e89800 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e89677 X0 X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e89677
              | (have j0 := b7e89677 X0 X1
                 grind)
              | exact resolve b7e89677 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e89677
            have b7e96641 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e1193 X0 (τ X0)
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e1193
              | exact resolve b7e1193 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e1193
            have b7e96859 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (k (τ X0) X1)) = X0 ∨ (σ X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e96641 X0 X1
                 have i₂ := b7e30 X0 X1
                 grind)
              | exact superpose b7e30 b7e96641
              | (have j0 := b7e96641 X0 X1
                 grind)
              | exact resolve b7e96641 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96641
            have b7e96871 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (k X0 (σ X1)) = X0 ∨ (σ X1) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e96859 X0 X1
                 have i₂ := b7e30 X0 X1
                 grind)
              | exact superpose b7e30 b7e96859
              | (have j0 := b7e96859 X0 X1
                 grind)
              | exact resolve b7e96859 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96859
            have b7e170290 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (τ X0))) (σ (τ X0))) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e1013 (τ X0) X1
                 have i₂ := b7e30 X0 (τ X0)
                 grind)
              | exact superpose b7e30 b7e1013
              | (have j0 := b7e1013 (τ X0) X1
                 grind)
              | exact resolve b7e1013 b7e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e30 b7e1013
            have b7e170855 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b7e170290 X0 X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e170290
              | (have j0 := b7e170290 X0 X1
                 grind)
              | exact resolve b7e170290 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e170290
            have b7e170948 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b7e170855 X0 X1
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e170855
              | (have j0 := b7e170855 X0 X1
                 grind)
              | exact resolve b7e170855 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e170855
            have b7e176788 : ∀ X0 X1 : G, (M.op y X1) = (k (M.op y X1) (M.op (M.op X0 X1) (M.op x X1))) := by
              intro X0 X1
              first
              | (have i₁ := b7e10964 x X1 y
                 have i₂ := b7e48 X1 X0
                 grind)
              | exact superpose b7e48 b7e10964
              | exact resolve b7e10964 b7e48
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e48 b7e10964
            have b7e230469 : x = (k x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
            clear b7e15444
            have b7e230472 : x = (k x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b7e230469
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e230469 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e230469
            have b7e231768 : x = (M.op x (M.op x x)) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e19 x (M.op x x)
                 have i₂ := b7e230472
                 grind)
              | exact superpose b7e230472 b7e19
              | (have j0 := b7e19 x (M.op x x)
                 grind)
              | exact resolve b7e19 b7e230472
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e230472
            have b7e231769 : x = (M.op x (M.op x x)) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b7e231768
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e231768 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231768
            have b7e231771 : x = (M.op y x) ∨ (M.op x x) = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e231769
                 have i₂ := b7e39 x
                 grind)
              | exact superpose b7e39 b7e231769
              | exact resolve b7e231769 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231769
            have b7e231773 : x = y ∨ (M.op x x) = (M.op (M.op x x) x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e231771
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e231771
              | exact resolve b7e231771 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231771
            have b7e231775 : (M.op x x) = (M.op x (M.op x x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e231773
                 have i₂ := b7e14 x x x
                 grind)
              | exact superpose b7e14 b7e231773
              | exact resolve b7e231773 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231773
            have b7e231777 : (M.op y x) = (M.op x x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e231775
                 have i₂ := b7e39 x
                 grind)
              | exact superpose b7e39 b7e231775
              | exact resolve b7e231775 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231775
            have b7e231779 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
              first
              | (have i₁ := b7e231777
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e231777
              | exact resolve b7e231777 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231777
            have b7e256880 : ∀ X0 : G, (M.op y X0) = (M.op (k x x) X0) ∨ x = (M.op x x) := by
              intro X0
              first
              | (have i₁ := b7e39 X0
                 have i₂ := b7e89800 x X0
                 grind)
              | exact superpose b7e89800 b7e39
              | (have j1 := b7e89800 x x
                 grind)
              | exact resolve b7e39 b7e89800
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e256953 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (k x x) (M.op X0 X1)) ∨ x = (M.op x x) := by
              intro X0 X1
              first
              | (have i₁ := b7e149 X0 X1 X0
                 have i₂ := b7e89800 x (M.op X0 X1)
                 grind)
              | exact superpose b7e89800 b7e149
              | (have j1 := b7e89800 x X1
                 grind)
              | exact resolve b7e149 b7e89800
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e149
            have b7e257727 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (k x x) (M.op X0 X1)) := by
              intro X0 X1
              first
              | (have j0 := b7e256953 X0 X1
                 grind)
              | (have r₁ := b7e256953 X0 X1
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e256953 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e256953
            have b7e257743 : ∀ X0 : G, (M.op y X0) = (M.op (k x x) X0) := by
              intro X0
              first
              | (have j0 := b7e256880 X0
                 grind)
              | (have r₁ := b7e256880 X0
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e256880 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e256880
            have b7e260738 : ∀ X0 X1 : G, (M.op X0 (M.op y X0)) = (M.op (M.op X1 (k x x)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e14 X0 (k x x) X1
                 have i₂ := b7e257743 X0
                 grind)
              | exact superpose b7e257743 b7e14
              | exact resolve b7e14 b7e257743
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e261012 : (M.op y (k x x)) = (M.op y (M.op x (k x x))) := by
              first
              | (have i₁ := b7e39 (k x x)
                 have i₂ := b7e257743 (M.op x (k x x))
                 grind)
              | exact superpose b7e257743 b7e39
              | exact resolve b7e39 b7e257743
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e257743
            have b7e261213 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 (k x x)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b7e260738 X0 X1
                 have i₂ := b7e96 X0
                 grind)
              | exact superpose b7e96 b7e260738
              | exact resolve b7e260738 b7e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e260738
            have b7e264813 : (M.op y (k x x)) = (k (M.op y (k x x)) (M.op y (M.op x (k x x)))) := by
              first
              | (have i₁ := b7e176788 x (k x x)
                 have i₂ := b7e261213 (M.op x (k x x)) x
                 grind)
              | exact superpose b7e261213 b7e176788
              | exact resolve b7e176788 b7e261213
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e176788 b7e261213
            have b7e265132 : (M.op y (k x x)) = (k (M.op y (k x x)) (M.op y (k x x))) := by
              first
              | (have i₁ := b7e264813
                 have i₂ := b7e261012
                 grind)
              | exact superpose b7e261012 b7e264813
              | exact resolve b7e264813 b7e261012
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e264813
            have b7e287120 : ∀ X0 : G, (k X0 (M.op X0 (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e10870 X0 x
                 have i₂ := b7e170948 X0 x
                 grind)
              | exact superpose b7e170948 b7e10870
              | (have j1 := b7e170948 X0 x
                 grind)
              | exact resolve b7e10870 b7e170948
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e10870
            have b7e287125 : (M.op y x) = (M.op x (k x x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b7e46 x x
                 have i₂ := b7e170948 x x
                 grind)
              | exact superpose b7e170948 b7e46
              | (have j1 := b7e170948 x x
                 grind)
              | exact resolve b7e46 b7e170948
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e46 b7e170948
            have b7e287575 : (M.op y x) = (M.op x (k x x)) := by
              first
              | (have r₁ := b7e287125
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e287125 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e287125
            have b7e287646 : y = (M.op x (k x x)) := by
              first
              | (have i₁ := b7e287575
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e287575
              | exact resolve b7e287575 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e287575
            have b7e290081 : (M.op y y) = (M.op y (k x x)) := by
              first
              | (have i₁ := b7e261012
                 have i₂ := b7e287646
                 grind)
              | exact superpose b7e287646 b7e261012
              | exact resolve b7e261012 b7e287646
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e261012
            have b7e293653 : (M.op (k x x) (M.op y y)) = (M.op (k y y) (k x x)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b7e89800 y (k x x)
                 have i₂ := b7e290081
                 grind)
              | exact superpose b7e290081 b7e89800
              | (have j0 := b7e89800 y x
                 grind)
              | exact resolve b7e89800 b7e290081
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e89800 b7e290081
            have b7e293663 : (M.op y (M.op y y)) = (M.op (k y y) (k x x)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b7e293653
                 have i₂ := b7e257727 y y
                 grind)
              | exact superpose b7e257727 b7e293653
              | exact resolve b7e293653 b7e257727
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e257727 b7e293653
            have b7e293796 : (M.op y y) = (M.op (k y y) (k x x)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b7e293663
                 have i₂ := b7e96 y
                 grind)
              | exact superpose b7e96 b7e293663
              | exact resolve b7e293663 b7e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96 b7e293663
            have b7e341182 : x = (k x (τ (σ x))) ∨ x = y ∨ y = (M.op x x) := by
              first
              | (have i₁ := b7e13802
                 have i₂ := b7e231779
                 grind)
              | exact superpose b7e231779 b7e13802
              | exact resolve b7e13802 b7e231779
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e231779
            have b7e341286 : x = (k x x) ∨ x = y ∨ y = (M.op x x) := by
              first
              | (have i₁ := b7e341182
                 have i₂ := b7e15 x
                 grind)
              | exact superpose b7e15 b7e341182
              | exact resolve b7e341182 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e341182
            have b7e344254 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = y ∨ y = (M.op x x) := by
              first
              | (have i₁ := b7e287120 x
                 have i₂ := b7e341286
                 grind)
              | exact superpose b7e341286 b7e287120
              | (have j0 := b7e287120 x
                 grind)
              | exact resolve b7e287120 b7e341286
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e287120 b7e341286
            have b7e344266 : x = (k x (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
              first
              | (have j1 := b7e55764 x
                 grind)
              | (have r₁ := b7e344254
                 have r₂ := b7e55764 x
                 grind)
              | exact resolve b7e344254 b7e55764
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e55764 b7e344254
            have b7e344275 : x = (k x (M.op x x)) ∨ x = y := by
              first
              | (have r₁ := b7e344266
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e344266 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e344266
            have b7e440722 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              first
              | (have i₁ := b7e96871 X0 (τ X0)
                 have i₂ := b7e16 X0
                 grind)
              | exact superpose b7e16 b7e96871
              | exact resolve b7e96871 b7e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e96871
            have b7e440770 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
              intro X0 X1
              first
              | (have j0 := b7e440722 X1 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e440722
            have b7e441281 : ∀ X0 : G, (M.op y X0) ≠ X0 ∨ (k X0 (M.op x X0)) = X0 ∨ (M.op x X0) = X0 := by
              intro X0
              first
              | (have i₁ := b7e440770 X0 (M.op x X0)
                 have i₂ := b7e39 X0
                 grind)
              | exact superpose b7e39 b7e440770
              | (have j0 := b7e440770 X0 (M.op x X0)
                 grind)
              | exact resolve b7e440770 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e440770
            have b7e449735 : x ≠ y ∨ x = (k x (M.op x x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b7e441281 x
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e441281
              | (have j0 := b7e441281 x
                 grind)
              | exact resolve b7e441281 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e441281
            have b7e449736 : x = (k x (M.op x x)) ∨ x = (M.op x x) := by
              first
              | (have r₁ := b7e449735
                 have r₂ := b7e344275
                 grind)
              | exact resolve b7e449735 b7e344275
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e344275 b7e449735
            have b7e449737 : x = (k x (M.op x x)) := by
              first
              | (have r₁ := b7e449736
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e449736 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449736
            have b7e449759 : (σ x) = (σ (M.op x (M.op x x))) ∨ x = (M.op x x) ∨ (M.op x x) = (M.op (M.op x x) x) := by
              first
              | (have i₁ := b7e54030 x (M.op x x)
                 have i₂ := b7e449737
                 grind)
              | exact superpose b7e449737 b7e54030
              | (have j0 := b7e54030 x (M.op x x)
                 grind)
              | exact resolve b7e54030 b7e449737
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e54030 b7e449737
            have b7e449762 : (σ x) = (σ (M.op x (M.op x x))) ∨ (M.op x x) = (M.op (M.op x x) x) := by
              first
              | (have r₁ := b7e449759
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e449759 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449759
            have b7e449766 : (σ x) = (σ (M.op y x)) ∨ (M.op x x) = (M.op (M.op x x) x) := by
              first
              | (have i₁ := b7e449762
                 have i₂ := b7e39 x
                 grind)
              | exact superpose b7e39 b7e449762
              | exact resolve b7e449762 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449762
            have b7e449770 : (σ x) = (σ y) ∨ (M.op x x) = (M.op (M.op x x) x) := by
              first
              | (have i₁ := b7e449766
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e449766
              | exact resolve b7e449766 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449766
            have b7e449774 : (M.op x x) = (M.op (M.op x x) x) := by
              first
              | (have r₁ := b7e449770
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e449770 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449770
            have b7e449778 : (M.op x x) = (M.op x (M.op x x)) := by
              first
              | (have i₁ := b7e449774
                 have i₂ := b7e14 x x x
                 grind)
              | exact superpose b7e14 b7e449774
              | exact resolve b7e449774 b7e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449774
            have b7e449782 : (M.op y x) = (M.op x x) := by
              first
              | (have i₁ := b7e449778
                 have i₂ := b7e39 x
                 grind)
              | exact superpose b7e39 b7e449778
              | exact resolve b7e449778 b7e39
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e39 b7e449778
            have b7e449785 : y = (M.op x x) := by
              first
              | (have i₁ := b7e449782
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e449782
              | exact resolve b7e449782 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449782
            have b7e450680 : x ≠ y ∨ x = (k x x) := by
              first
              | (have i₁ := b7e17 x x
                 have i₂ := b7e449785
                 grind)
              | exact superpose b7e449785 b7e17
              | (have j0 := b7e17 x x
                 grind)
              | exact resolve b7e17 b7e449785
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b7e495002 : (σ x) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
              first
              | (have i₁ := b7e10594
                 have i₂ := b7e23914 x
                 grind)
              | exact superpose b7e23914 b7e10594
              | (have j1 := b7e23914 (σ x)
                 grind)
              | exact resolve b7e10594 b7e23914
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e10594 b7e23914
            have b7e495153 : (σ x) = (M.op (σ (M.op x x)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b7e495002
                 have r₂ := b7e25
                 grind)
              | exact resolve b7e495002 b7e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e495002
            have b7e495174 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e495153
                 have i₂ := b7e449785
                 grind)
              | exact superpose b7e449785 b7e495153
              | exact resolve b7e495153 b7e449785
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e449785 b7e495153
            have b7e496556 : (k y y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have i₁ := b7e687 y
                 have i₂ := b7e495174
                 grind)
              | exact superpose b7e495174 b7e687
              | (have j0 := b7e687 x
                 grind)
              | exact resolve b7e687 b7e495174
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e687 b7e495174
            have b7e496715 : (k y y) = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
              first
              | (have r₁ := b7e496556
                 have r₂ := b7e24
                 grind)
              | exact resolve b7e496556 b7e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e496556
            have b7e496741 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k y y) := by
              first
              | (have i₁ := b7e496715
                 have i₂ := b7e15 x
                 grind)
              | exact superpose b7e15 b7e496715
              | exact resolve b7e496715 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e496715
            have b7e497938 : x = (k x (τ (σ x))) ∨ x = (k y y) := by
              first
              | (have i₁ := b7e13802
                 have i₂ := b7e496741
                 grind)
              | exact superpose b7e496741 b7e13802
              | exact resolve b7e13802 b7e496741
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e13802 b7e496741
            have b7e498213 : x = (k y y) ∨ x = (k x x) := by
              first
              | (have i₁ := b7e497938
                 have i₂ := b7e15 x
                 grind)
              | exact superpose b7e15 b7e497938
              | exact resolve b7e497938 b7e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e497938
            have b7e499777 : (M.op y y) = (M.op x (k x x)) ∨ y = (M.op y y) ∨ x = (k x x) := by
              first
              | (have i₁ := b7e293796
                 have i₂ := b7e498213
                 grind)
              | exact superpose b7e498213 b7e293796
              | exact resolve b7e293796 b7e498213
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e293796
            have b7e499824 : y = (M.op y y) ∨ y = (M.op y y) ∨ x = (k x x) := by
              first
              | (have i₁ := b7e499777
                 have i₂ := b7e287646
                 grind)
              | exact superpose b7e287646 b7e499777
              | exact resolve b7e499777 b7e287646
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e287646 b7e499777
            have b7e499825 : x = (k x x) ∨ y = (M.op y y) := by grind
            clear b7e499824
            have b7e501154 : (M.op y x) = (k (M.op y x) (M.op y x)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b7e265132
                 have i₂ := b7e499825
                 grind)
              | exact superpose b7e499825 b7e265132
              | exact resolve b7e265132 b7e499825
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e265132 b7e499825
            have b7e501201 : y = (k y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b7e501154
                 have i₂ := b7e22
                 grind)
              | exact superpose b7e22 b7e501154
              | exact resolve b7e501154 b7e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e501154
            have b7e501220 : y = (k y y) := by
              first
              | (have j1 := b7e17 y y
                 grind)
              | (have r₁ := b7e501201
                 have r₂ := b7e17 y y
                 grind)
              | exact resolve b7e501201 b7e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e501201
            have b7e503889 : x = y ∨ x = (k x x) := by
              first
              | (have i₁ := b7e498213
                 have i₂ := b7e501220
                 grind)
              | exact superpose b7e501220 b7e498213
              | exact resolve b7e498213 b7e501220
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e498213 b7e501220
            have b7e503919 : x = (k x x) := by
              first
              | (have r₁ := b7e503889
                 have r₂ := b7e450680
                 grind)
              | exact resolve b7e503889 b7e450680
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e450680 b7e503889
            have b7e504773 : x ≠ x ∨ x = (M.op x x) := by
              first
              | (have i₁ := b7e10422 x
                 have i₂ := b7e503919
                 grind)
              | exact superpose b7e503919 b7e10422
              | (have j0 := b7e10422 x
                 grind)
              | (have r₁ := b7e10422 x
                 have r₂ := b7e503919
                 grind)
              | exact resolve b7e10422 b7e503919
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b7e10422 b7e503919
            have b7e504788 : x = (M.op x x) := by grind
            clear b7e504773
            have b7e504798 : False := by grind
            exact b7e504798
          · have b8e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b h2a h2b
            have b8e28 : False := by grind
            exact b8e28
  · rcases eq_or_ne (x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b9e21 : y ≠ (M.op y x) := by grind
          have b9e22 : x = y := by grind
          have b9e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b9e30 : False := by grind
          exact b9e30
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b10e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b10e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b10e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b10e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b10e23 : x = y := by grind
            have b10e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b10e25 : x ≠ (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b10e34 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) := by grind
            have b10e35 : (σ y) = (k (σ y) (σ y)) := by grind
            clear b10e34
            have b10e36 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b10e35
                 have i₂ := b10e20 y y
                 grind)
              | exact superpose b10e20 b10e35
              | exact resolve b10e35 b10e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e35
            have b10e37 : (k y y) = (τ (σ y)) := by
              first
              | (have i₁ := b10e15 (k y y)
                 have i₂ := b10e36
                 grind)
              | exact superpose b10e36 b10e15
              | exact resolve b10e15 b10e36
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e36
            have b10e38 : y = (k y y) := by
              first
              | (have i₁ := b10e37
                 have i₂ := b10e15 y
                 grind)
              | exact superpose b10e15 b10e37
              | exact resolve b10e37 b10e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b10e37
            have b10e63 : y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b10e38
            have b10e65 : y = (M.op y y) := by grind
            clear b10e63
            have b10e68 : False := by grind
            exact b10e68
          · have b11e23 : x = y := by grind
            have b11e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b11e33 : False := by grind
            exact b11e33
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b12e22 : y ≠ (M.op y x) := by grind
            have b12e23 : x = y := by grind
            have b12e26 : x = (M.op x x) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b12e33 : False := by grind
            exact b12e33
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b13e19 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
                intro X0 X1
                grind
              have b13e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b13e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b13e24 : x = y := by grind
              have b13e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b13e27 : x ≠ (M.op x x) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b13e50 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
                intro X0
                grind
              have b13e1251 : (σ (M.op y y)) ≠ (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
              clear b13e50
              have b13e1279 : (σ (M.op y y)) ≠ (σ (k y y)) := by grind
              clear b13e1251
              have b13e1283 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ y = (M.op y y) := by grind
              clear b13e1279
              have b13e1284 : y = (M.op y y) := by grind
              clear b13e1283
              have b13e1285 : False := by grind
              exact b13e1285
            · have b14e24 : x = y := by grind
              have b14e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b14e36 : False := by grind
              exact b14e36
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b15e23 : x = y := by grind
            have b15e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b15e33 : False := by grind
            exact b15e33
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b16e24 : x = y := by grind
              have b16e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b16e36 : False := by grind
              exact b16e36
            · have b17e24 : x = y := by grind
              have b17e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b17e36 : False := by grind
              exact b17e36
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
        · have b18e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
            intro X0 X1 X2
            grind
          have b18e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b18e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b18e17 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
            intro X0 X1
            grind
          have b18e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b18e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b18e21 : y ≠ (M.op y x) := by grind
          have b18e22 : x ≠ y := by grind
          have b18e23 : (σ y) = (M.op (σ y) (σ x)) := by grind
          have b18e24 : x = (M.op x x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a
          have b18e26 : x ≠ x ∨ x = (k x x) := by
            first
            | (have i₁ := b18e16 x x
               have i₂ := b18e24
               grind)
            | exact superpose b18e24 b18e16
            | (have j0 := b18e16 x x
               grind)
            | (have r₁ := b18e16 x x
               have r₂ := b18e24
               grind)
            | exact resolve b18e16 b18e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
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
          have b18e29 : x = (k x x) := by grind
          clear b18e26
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
          have b18e41 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
            intro X0
            first
            | (have i₁ := b18e13 (σ x) (σ y) X0
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X2 X1 X3
               have i₂ := b18e13 X2 X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e43 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e13 X3 (M.op X1 X2) X2
               have i₂ := b18e13 X2 X1 X0
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e44 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X2 X0 (M.op x X1)
               have i₂ := b18e13 X0 X1 x
               grind)
            | exact superpose b18e13 b18e13
            | exact resolve b18e13 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e45 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 (σ x) (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e13
            | exact resolve b18e13 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e51 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            grind
          have b18e66 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) := by
            first
            | (have i₁ := b18e36
               have i₂ := b18e18 x y
               grind)
            | exact superpose b18e18 b18e36
            | (have j1 := b18e18 x y
               grind)
            | exact resolve b18e36 b18e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e36
          have b18e69 : x = (M.op x y) ∨ y = (M.op y x) := by
            first
            | (have r₁ := b18e66
               have r₂ := b18e22
               grind)
            | exact resolve b18e66 b18e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e66
          have b18e72 : x = (M.op x y) := by
            first
            | (have r₁ := b18e69
               have r₂ := b18e21
               grind)
            | exact resolve b18e69 b18e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e69
          have b18e75 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op y X0)) := by
            intro X0
            first
            | (have i₁ := b18e13 X0 y x
               have i₂ := b18e72
               grind)
            | exact superpose b18e72 b18e13
            | exact resolve b18e13 b18e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e120 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b18e42 X0 (σ x) X1 (σ y)
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e42
            | exact resolve b18e42 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e137 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = X2 := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b18e16 X2 (M.op X3 X1)
               have i₂ := b18e42 X3 X1 X2 X0
               grind)
            | (have i₁ := b18e16 X2 (M.op X3 X1)
               have i₂ := b18e42 X0 X1 X2 X3
               grind)
            | exact superpose b18e42 b18e16
            | (have j0 := b18e16 X2 (M.op X3 X1)
               grind)
            | (have r₁ := b18e16 X2 (M.op (M.op X3 X2) X2)
               have r₂ := b18e42 (M.op X3 X2) X2 X2 X3
               grind)
            | (have r₁ := b18e16 X2 (M.op (M.op X0 X2) X2)
               have r₂ := b18e42 X0 X2 X2 (M.op X0 X2)
               grind)
            | exact resolve b18e16 b18e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e156 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op (σ x) X0)) X1) = (M.op (M.op (σ y) X0) X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e42 X0 (M.op (σ x) X0) X1 X2
               have i₂ := b18e45 X0
               grind)
            | exact superpose b18e45 b18e42
            | exact resolve b18e42 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e42
          have b18e259 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
            intro X0
            first
            | (have i₁ := b18e44 (σ x) (M.op x (σ y)) X0
               have i₂ := b18e41 x
               grind)
            | exact superpose b18e41 b18e44
            | exact resolve b18e44 b18e41
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e294 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b18e13 X0 (M.op X2 X1) X1
               have i₂ := b18e44 X1 X2 X0
               grind)
            | exact superpose b18e44 b18e13
            | exact resolve b18e13 b18e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e44
          have b18e301 : ∀ X0 : G, (M.op X0 (M.op (σ x) X0)) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b18e259 X0
               have i₂ := b18e156 (σ y) X0 (σ x)
               grind)
            | exact superpose b18e156 b18e259
            | exact resolve b18e259 b18e156
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e156 b18e259
          have b18e306 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b18e301 X0
               have i₂ := b18e45 X0
               grind)
            | exact superpose b18e45 b18e301
            | exact resolve b18e301 b18e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e45 b18e301
          have b18e567 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0 X1
            first
            | (have i₁ := b18e43 X1 (σ y) (σ x) X0
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e43
            | exact resolve b18e43 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b18e677 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
            intro X0 X1
            first
            | (have i₁ := b18e41 (M.op (M.op x X0) X1)
               have i₂ := b18e43 x X0 X1 (σ y)
               grind)
            | exact superpose b18e43 b18e41
            | exact resolve b18e41 b18e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e41 b18e43
          have b18e680 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
            intro X0 X1
            first
            | (have i₁ := b18e677 X0 X1
               have i₂ := b18e13 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
               grind)
            | exact superpose b18e13 b18e677
            | exact resolve b18e677 b18e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e677
          have b18e722 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
            intro X0
            first
            | (have i₁ := b18e567 X0 x
               have i₂ := b18e120 (M.op x (σ y)) X0
               grind)
            | exact superpose b18e120 b18e567
            | exact resolve b18e567 b18e120
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e567
          have b18e728 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
            first
            | (have i₁ := b18e680 x x
               have i₂ := b18e294 (σ x) (σ y) (M.op x x)
               grind)
            | exact superpose b18e294 b18e680
            | exact resolve b18e680 b18e294
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e294 b18e680
          have b18e743 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b18e728
               have i₂ := b18e722 (σ x)
               grind)
            | exact superpose b18e722 b18e728
            | exact resolve b18e728 b18e722
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e722 b18e728
          have b18e746 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b18e743
               have i₂ := b18e23
               grind)
            | exact superpose b18e23 b18e743
            | exact resolve b18e743 b18e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e743
          have b18e1173 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have j0 := b18e51 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e51
          have b18e14831 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b18e1173 x
               have i₂ := b18e29
               grind)
            | exact superpose b18e29 b18e1173
            | (have j0 := b18e1173 x
               grind)
            | exact resolve b18e1173 b18e29
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e29 b18e1173
          have b18e14834 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear b18e14831
          have b18e14848 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) := by
            intro X0
            first
            | (have i₁ := b18e120 (σ x) X0
               have i₂ := b18e14834
               grind)
            | exact superpose b18e14834 b18e120
            | exact resolve b18e120 b18e14834
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e120 b18e14834
          have b18e15115 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
            intro X0 X1
            first
            | (have j0 := b18e137 X0 X0 X0 (M.op X1 X0)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e137
          have b18e15264 : (σ y) = (k (σ y) (M.op (σ y) (σ y))) := by
            first
            | (have i₁ := b18e15115 (σ y) (σ y)
               have i₂ := b18e306 (σ y)
               grind)
            | exact superpose b18e306 b18e15115
            | exact resolve b18e15115 b18e306
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e306 b18e15115
          have b18e15283 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) := by
            first
            | (have i₁ := b18e15264
               have i₂ := b18e14848 (σ y)
               grind)
            | exact superpose b18e14848 b18e15264
            | exact resolve b18e15264 b18e14848
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e14848 b18e15264
          have b18e15311 : (σ y) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b18e15283
               have i₂ := b18e746
               grind)
            | exact superpose b18e746 b18e15283
            | exact resolve b18e15283 b18e746
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e746 b18e15283
          have b18e15325 : (σ y) = (σ (k y y)) := by
            first
            | (have i₁ := b18e15311
               have i₂ := b18e19 y y
               grind)
            | exact superpose b18e19 b18e15311
            | exact resolve b18e15311 b18e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e15311
          have b18e15388 : (k y y) = (τ (σ y)) := by
            first
            | (have i₁ := b18e14 (k y y)
               have i₂ := b18e15325
               grind)
            | exact superpose b18e15325 b18e14
            | exact resolve b18e14 b18e15325
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e15325
          have b18e15424 : y = (k y y) := by
            first
            | (have i₁ := b18e15388
               have i₂ := b18e14 y
               grind)
            | exact superpose b18e14 b18e15388
            | exact resolve b18e15388 b18e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e15388
          have b18e16328 : y = (M.op y y) ∨ y = (M.op y y) := by grind
          clear b18e15424
          have b18e16329 : y = (M.op y y) := by grind
          clear b18e16328
          have b18e16398 : (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b18e75 y
               have i₂ := b18e16329
               grind)
            | exact superpose b18e16329 b18e75
            | exact resolve b18e75 b18e16329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e75
          have b18e16443 : y = (M.op x y) := by
            first
            | (have i₁ := b18e16398
               have i₂ := b18e16329
               grind)
            | exact superpose b18e16329 b18e16398
            | exact resolve b18e16398 b18e16329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e16329 b18e16398
          have b18e16448 : x = y := by
            first
            | (have i₁ := b18e16443
               have i₂ := b18e72
               grind)
            | exact superpose b18e72 b18e16443
            | exact resolve b18e16443 b18e72
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b18e72 b18e16443
          have b18e16451 : False := by grind
          exact b18e16451
        · rcases eq_or_ne (x) (x) with h2b | h2b
          · have b19e14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X1) X0) := by
              intro X0 X1 X2
              grind
            have b19e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b19e16 : ∀ X0 : G, (σ (τ X0)) = X0 := by
              intro X0
              grind
            have b19e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
              intro X0 X1
              grind
            have b19e18 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
              intro X0 X1
              grind
            have b19e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b19e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b19e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b19e22 : y ≠ (M.op y x) := by grind
            have b19e23 : x ≠ y := by grind
            have b19e24 : (σ y) = (M.op (σ y) (σ x)) := by grind
            have b19e25 : x ≠ (M.op x x) := by grind
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
            have b19e30 : (σ x) = (σ (k x y)) := by
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
            have b19e31 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 (τ X0) X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e20
              | exact resolve b19e20 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e32 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X1 (τ X0)
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e20
              | exact resolve b19e20 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e35 : (k x y) = (τ (σ x)) := by
              first
              | (have i₁ := b19e15 (k x y)
                 have i₂ := b19e30
                 grind)
              | exact superpose b19e30 b19e15
              | exact resolve b19e15 b19e30
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e36 : x = (k x y) := by
              first
              | (have i₁ := b19e35
                 have i₂ := b19e15 x
                 grind)
              | exact superpose b19e15 b19e35
              | exact resolve b19e35 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e35
            have b19e39 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) (σ x)) := by
              intro X0
              first
              | (have i₁ := b19e14 (σ x) (σ y) X0
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e14
              | exact resolve b19e14 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e41 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X1)) X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X0 (M.op X2 X1) X3
                 have i₂ := b19e14 X0 X1 X2
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e42 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X2 X1 X3
                 have i₂ := b19e14 X2 X1 X0
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e44 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op (M.op X1 X2) X3)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e14 X3 (M.op X1 X2) X2
                 have i₂ := b19e14 X2 X1 X0
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e45 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X2)) = (M.op (M.op X0 (M.op X1 X0)) X2) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 X2 X0 (M.op x X1)
                 have i₂ := b19e14 X0 X1 x
                 grind)
              | exact superpose b19e14 b19e14
              | exact resolve b19e14 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e51 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
              intro X0 X1
              first
              | (have i₁ := b19e15 (k (τ X0) X1)
                 have i₂ := b19e31 X0 X1
                 grind)
              | exact superpose b19e31 b19e15
              | exact resolve b19e15 b19e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e53 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b19e54 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              grind
            have b19e55 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
              intro X0
              first
              | (have i₁ := b19e54 X0
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e54
              | (have j0 := b19e54 X0
                 grind)
              | exact resolve b19e54 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e54
            have b19e62 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e15 (k X0 (τ X1))
                 have i₂ := b19e32 X1 X0
                 grind)
              | exact superpose b19e32 b19e15
              | exact resolve b19e15 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e20 X0 X1
                 have i₂ := b19e19 (σ X0) (σ X1)
                 grind)
              | exact superpose b19e19 b19e20
              | (have j1 := b19e19 (σ X0) (σ X1)
                 grind)
              | exact resolve b19e20 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e71 : x = (M.op x y) ∨ x = y ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e36
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e36
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e36 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e36
            have b19e72 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op y x) := by
              first
              | (have i₁ := b19e30
                 have i₂ := b19e19 x y
                 grind)
              | exact superpose b19e19 b19e30
              | (have j1 := b19e19 x y
                 grind)
              | exact resolve b19e30 b19e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e30
            have b19e73 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b19e72
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e72 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e72
            have b19e74 : x = (M.op x y) ∨ y = (M.op y x) := by
              first
              | (have r₁ := b19e71
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e71 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e71
            have b19e76 : (σ (M.op x y)) = (σ x) := by
              first
              | (have r₁ := b19e73
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e73 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e73
            have b19e77 : x = (M.op x y) := by
              first
              | (have r₁ := b19e74
                 have r₂ := b19e22
                 grind)
              | exact resolve b19e74 b19e22
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e74
            have b19e79 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op x X0) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 y x
                 have i₂ := b19e77
                 grind)
              | exact superpose b19e77 b19e14
              | exact resolve b19e14 b19e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e95 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X0)) X3) = (M.op (M.op X2 X0) X3) := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e42 X2 X0 X3 (M.op x X1)
                 have i₂ := b19e14 X0 X1 x
                 grind)
              | exact superpose b19e14 b19e42
              | exact resolve b19e42 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e96 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) X1) = (M.op (σ y) X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e42 X0 (σ x) X1 (σ y)
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e42
              | exact resolve b19e42 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e97 : ∀ X0 X1 : G, (M.op (M.op X0 y) X1) = (M.op x X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e42 X0 y X1 x
                 have i₂ := b19e77
                 grind)
              | exact superpose b19e77 b19e42
              | exact resolve b19e42 b19e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e109 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X3 X1) ∨ (k X2 (M.op X3 X1)) = X2 := by
              intro X0 X1 X2 X3
              first
              | (have i₁ := b19e17 X2 (M.op X3 X1)
                 have i₂ := b19e42 X3 X1 X2 X0
                 grind)
              | (have i₁ := b19e17 X2 (M.op X3 X1)
                 have i₂ := b19e42 X0 X1 X2 X3
                 grind)
              | exact superpose b19e42 b19e17
              | (have j0 := b19e17 X2 (M.op X3 X1)
                 grind)
              | (have r₁ := b19e17 X2 (M.op (M.op X3 X2) X2)
                 have r₂ := b19e42 (M.op X3 X2) X2 X2 X3
                 grind)
              | (have r₁ := b19e17 X2 (M.op (M.op X0 X2) X2)
                 have r₂ := b19e42 X0 X2 X2 (M.op X0 X2)
                 grind)
              | exact resolve b19e17 b19e42
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e223 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op (M.op X2 X1) X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 X0 (M.op X2 X1) X1
                 have i₂ := b19e45 X1 X2 X0
                 grind)
              | exact superpose b19e45 b19e14
              | exact resolve b19e14 b19e45
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e324 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
              intro X0 X1
              first
              | (have i₁ := b19e45 X1 x X0
                 have i₂ := b19e41 X0 X1 x X1
                 grind)
              | exact superpose b19e41 b19e45
              | exact resolve b19e45 b19e41
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e41 b19e45
            have b19e458 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) (σ x)) X0) = (M.op X0 (M.op (σ y) X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e44 X1 (σ y) (σ x) X0
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e44
              | exact resolve b19e44 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e551 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op (M.op X1 X2) X0)) = (M.op (M.op X4 X2) X0) := by
              intro X0 X1 X2 X4
              first
              | (have i₁ := b19e42 (M.op x X1) X2 X0 X4
                 have i₂ := b19e44 x X1 X2 X0
                 grind)
              | exact superpose b19e44 b19e42
              | exact resolve b19e42 b19e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e557 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (M.op X0 X1) (σ y))) (σ x)) := by
              intro X0 X1
              first
              | (have i₁ := b19e39 (M.op (M.op x X0) X1)
                 have i₂ := b19e44 x X0 X1 (σ y)
                 grind)
              | exact superpose b19e44 b19e39
              | exact resolve b19e39 b19e44
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e39 b19e44
            have b19e559 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (M.op X0 X1) (σ y)) (σ x))) := by
              intro X0 X1
              first
              | (have i₁ := b19e557 X0 X1
                 have i₂ := b19e14 (σ x) (M.op (M.op X0 X1) (σ y)) (σ y)
                 grind)
              | exact superpose b19e14 b19e557
              | exact resolve b19e557 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e557
            have b19e597 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ y) X0)) := by
              intro X0
              first
              | (have i₁ := b19e458 X0 x
                 have i₂ := b19e96 (M.op x (σ y)) X0
                 grind)
              | exact superpose b19e96 b19e458
              | exact resolve b19e458 b19e96
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e96 b19e458
            have b19e603 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) (σ x))) := by
              first
              | (have i₁ := b19e559 x x
                 have i₂ := b19e223 (σ x) (σ y) (M.op x x)
                 grind)
              | exact superpose b19e223 b19e559
              | exact resolve b19e559 b19e223
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e223 b19e559
            have b19e618 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
              first
              | (have i₁ := b19e603
                 have i₂ := b19e597 (σ x)
                 grind)
              | exact superpose b19e597 b19e603
              | exact resolve b19e603 b19e597
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e603
            have b19e623 : (σ y) = (M.op (σ x) (σ y)) := by
              first
              | (have i₁ := b19e618
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e618
              | exact resolve b19e618 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e618
            have b19e624 : (σ (M.op x y)) ≠ (σ y) := by
              first
              | (have i₁ := b19e21
                 have i₂ := b19e623
                 grind)
              | exact superpose b19e623 b19e21
              | exact resolve b19e21 b19e623
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e623
            have b19e638 : (σ x) ≠ (σ y) := by
              first
              | (have i₁ := b19e624
                 have i₂ := b19e76
                 grind)
              | exact superpose b19e76 b19e624
              | exact resolve b19e624 b19e76
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e76 b19e624
            have b19e1115 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 (σ X0) (σ X0) X1
                 have i₂ := b19e53 X0
                 grind)
              | exact superpose b19e53 b19e14
              | (have j1 := b19e53 X0
                 grind)
              | exact resolve b19e14 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1116 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) X1)) = (M.op (σ (k X0 X0)) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X1 (σ X0) (σ X0)
                 have i₂ := b19e53 X0
                 grind)
              | exact superpose b19e53 b19e14
              | (have j1 := b19e53 X0
                 grind)
              | exact resolve b19e14 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1124 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X0)) X2) = (M.op (M.op X1 (σ X0)) X2) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e42 X1 (σ X0) X2 (σ X0)
                 have i₂ := b19e53 X0
                 grind)
              | exact superpose b19e53 b19e42
              | (have j1 := b19e53 X0
                 grind)
              | exact resolve b19e42 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1131 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have j0 := b19e53 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1226 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e69 X1 X0
                 have i₂ := b19e69 X0 X1
                 grind)
              | exact superpose b19e69 b19e69
              | (have j0 := b19e69 X1 X0
                 have j1 := b19e69 X1 X0
                 grind)
              | exact resolve b19e69 b19e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1249 : ∀ X0 X1 X2 : G, (M.op (σ X1) (σ X0)) = (M.op (M.op X2 (σ X0)) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e14 (σ X1) (σ X0) X2
                 have i₂ := b19e69 X1 X0
                 grind)
              | exact superpose b19e69 b19e14
              | (have j1 := b19e69 X1 X0
                 grind)
              | exact resolve b19e14 b19e69
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e69
            have b19e1268 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
              intro X0 X1
              first
              | (have j0 := b19e1226 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1226
            have b19e1307 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
              intro X0 X1
              first
              | (have i₁ := b19e51 X1 (τ X0)
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e51
              | exact resolve b19e51 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e1312 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              grind
            have b19e1319 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b19e1312 X0
                 have i₂ := b19e15 X0
                 grind)
              | exact superpose b19e15 b19e1312
              | (have j0 := b19e1312 X0
                 grind)
              | exact resolve b19e1312 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1312
            have b19e2098 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 (M.op X4 X1)) X2) := by
              intro X0 X1 X2 X3 X4
              first
              | (have i₁ := b19e42 X3 (M.op X4 X1) X2 X1
                 have i₂ := b19e95 X1 X4 X0 X2
                 grind)
              | exact superpose b19e95 b19e42
              | exact resolve b19e42 b19e95
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e42 b19e95
            have b19e3283 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) ≠ X0 ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X0 (M.op X1 X0)) X0) := by
              intro X0 X1
              first
              | (have i₁ := b19e17 (M.op X0 (M.op X1 X0)) X0
                 have i₂ := b19e324 X0 X1
                 grind)
              | exact superpose b19e324 b19e17
              | (have j0 := b19e17 (M.op X1 X0) X0
                 grind)
              | exact resolve b19e17 b19e324
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e14797 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b19e1131 (τ X0)
                 have i₂ := b19e32 X0 (τ X0)
                 grind)
              | exact superpose b19e32 b19e1131
              | (have j0 := b19e1131 (τ X0)
                 grind)
              | exact resolve b19e1131 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1131
            have b19e14798 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0
              first
              | (have i₁ := b19e14797 X0
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e14797
              | (have j0 := b19e14797 X0
                 grind)
              | exact resolve b19e14797 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e14797
            have b19e14801 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e14798 X0
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e14798
              | (have j0 := b19e14798 X0
                 grind)
              | exact resolve b19e14798 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e14798
            have b19e15028 : ∀ X0 X1 : G, (k X0 (M.op (M.op X1 X0) X0)) = X0 := by
              intro X0 X1
              first
              | (have j0 := b19e109 X0 X0 X0 (M.op X1 X0)
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e109
            have b19e15139 : ∀ X0 : G, (k X0 (M.op X0 (M.op X0 X0))) = X0 := by
              intro X0
              first
              | (have i₁ := b19e15028 X0 x
                 have i₂ := b19e14 X0 X0 x
                 grind)
              | exact superpose b19e14 b19e15028
              | exact resolve b19e15028 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e15166 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (k (M.op X2 X1) (M.op (M.op X0 X1) (M.op X2 X1))) := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e15028 (M.op X2 X1) x
                 have i₂ := b19e2098 X0 X1 (M.op X2 X1) x X2
                 grind)
              | exact superpose b19e2098 b19e15028
              | exact resolve b19e15028 b19e2098
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e2098 b19e15028
            have b19e16214 : ∀ X0 : G, (σ X0) = (k (σ X0) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
              intro X0
              first
              | (have i₁ := b19e15139 (σ X0)
                 have i₂ := b19e53 X0
                 grind)
              | exact superpose b19e53 b19e15139
              | (have j1 := b19e53 X0
                 grind)
              | exact resolve b19e15139 b19e53
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e53
            have b19e26783 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e55 (σ X0)
                 have i₂ := b19e15 X0
                 grind)
              | exact superpose b19e15 b19e55
              | exact resolve b19e55 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e55
            have b19e26806 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e26783 X0
                 have i₂ := b19e20 X0 X0
                 grind)
              | exact superpose b19e20 b19e26783
              | (have j0 := b19e26783 X0
                 grind)
              | exact resolve b19e26783 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e26783
            have b19e28996 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (τ (k (σ (M.op X0 X0)) X1)) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e62 (k X0 X0) X1
                 have i₂ := b19e26806 X0
                 grind)
              | exact superpose b19e26806 b19e62
              | (have j1 := b19e26806 X0
                 grind)
              | exact resolve b19e62 b19e26806
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e26806
            have b19e29003 : ∀ X0 X1 : G, (k (k X0 X0) (τ X1)) = (k (M.op X0 X0) (τ X1)) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e28996 X0 X1
                 have i₂ := b19e62 (M.op X0 X0) X1
                 grind)
              | exact superpose b19e62 b19e28996
              | (have j0 := b19e28996 X0 X1
                 grind)
              | exact resolve b19e28996 b19e62
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e62 b19e28996
            have b19e94519 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (τ X0)) X1)) = (M.op (k (σ (τ X0)) X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b19e1116 (τ X0) X1
                 have i₂ := b19e32 X0 (τ X0)
                 grind)
              | exact superpose b19e32 b19e1116
              | (have j0 := b19e1116 (τ X0) X1
                 grind)
              | exact resolve b19e1116 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1116
            have b19e95244 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (k X0 X0) X1) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b19e94519 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e94519
              | (have j0 := b19e94519 X0 X1
                 grind)
              | exact resolve b19e94519 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e94519
            have b19e95359 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e95244 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e95244
              | (have j0 := b19e95244 X0 X1
                 grind)
              | exact resolve b19e95244 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e95244
            have b19e95887 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (σ (k (τ X0) (τ X0))) X1) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e1124 (τ X0) X1 X2
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e1124
              | exact resolve b19e1124 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1124
            have b19e96837 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (k (σ (τ X0)) X0) X1) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e95887 X0 X1 X2
                 have i₂ := b19e32 X0 (τ X0)
                 grind)
              | exact superpose b19e32 b19e95887
              | (have j0 := b19e95887 X0 X1 X2
                 grind)
              | exact resolve b19e95887 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e95887
            have b19e96886 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X1) = (M.op (k X0 X0) X1) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e96837 X0 X1 X2
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e96837
              | (have j0 := b19e96837 X0 X1 X2
                 grind)
              | exact resolve b19e96837 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e96837
            have b19e175293 : ∀ X0 X1 : G, (M.op (M.op X1 (σ (τ X0))) (σ (τ X0))) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b19e1115 (τ X0) X1
                 have i₂ := b19e32 X0 (τ X0)
                 grind)
              | exact superpose b19e32 b19e1115
              | (have j0 := b19e1115 (τ X0) X1
                 grind)
              | exact resolve b19e1115 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1115
            have b19e175887 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
              intro X0 X1
              first
              | (have i₁ := b19e175293 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e175293
              | (have j0 := b19e175293 X0 X1
                 grind)
              | exact resolve b19e175293 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e175293
            have b19e175974 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e175887 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e175887
              | (have j0 := b19e175887 X0 X1
                 grind)
              | exact resolve b19e175887 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e175887
            have b19e183527 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op X1 (M.op (k X0 X0) X1)) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e324 X1 X0
                 have i₂ := b19e95359 X0 X1
                 grind)
              | exact superpose b19e95359 b19e324
              | (have j1 := b19e95359 X0 X1
                 grind)
              | exact resolve b19e324 b19e95359
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e263892 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) (M.op (k X0 X0) (M.op X1 X0))) ∨ (M.op X0 X0) = X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e15166 x X0 X1
                 have i₂ := b19e96886 X0 (M.op X1 X0) x
                 grind)
              | exact superpose b19e96886 b19e15166
              | (have j1 := b19e96886 X0 X1 x
                 grind)
              | exact resolve b19e15166 b19e96886
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e15166
            have b19e270471 : (M.op x y) = (M.op y (k y y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e97 x y
                 have i₂ := b19e175974 y x
                 grind)
              | exact superpose b19e175974 b19e97
              | (have j1 := b19e175974 y x
                 grind)
              | exact resolve b19e97 b19e175974
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e97
            have b19e270714 : ∀ X0 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X0 (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
              intro X0 X2
              first
              | (have i₁ := b19e551 X0 x X0 X2
                 have i₂ := b19e175974 X0 x
                 grind)
              | exact superpose b19e175974 b19e551
              | (have j1 := b19e175974 X0 x
                 grind)
              | exact resolve b19e551 b19e175974
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e551
            have b19e270735 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e96886 X0 X0 x
                 have i₂ := b19e175974 X0 x
                 grind)
              | exact superpose b19e175974 b19e96886
              | (have j0 := b19e96886 X0 x x
                 have j1 := b19e175974 X0 x
                 grind)
              | exact resolve b19e96886 b19e175974
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e175974
            have b19e271093 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b19e270735 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e270735
            have b19e271364 : x = (M.op y (k y y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e270471
                 have i₂ := b19e77
                 grind)
              | exact superpose b19e77 b19e270471
              | exact resolve b19e270471 b19e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e270471
            have b19e274845 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (k y y) X0)) ∨ y = (M.op y y) := by
              intro X0
              first
              | (have i₁ := b19e14 X0 (k y y) y
                 have i₂ := b19e271364
                 grind)
              | exact superpose b19e271364 b19e14
              | exact resolve b19e14 b19e271364
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b19e275012 : (M.op (k y y) x) = (M.op (k y y) (k y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e95359 y (k y y)
                 have i₂ := b19e271364
                 grind)
              | exact superpose b19e271364 b19e95359
              | (have j0 := b19e95359 y x
                 grind)
              | exact resolve b19e95359 b19e271364
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e95359 b19e271364
            have b19e275017 : (M.op (k y y) x) = (M.op (k y y) (k y y)) ∨ y = (M.op y y) := by grind
            clear b19e275012
            have b19e306479 : (M.op x y) = (M.op y (M.op y (k y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e274845 y
                 have i₂ := b19e271093 y
                 grind)
              | exact superpose b19e271093 b19e274845
              | (have j1 := b19e271093 y
                 grind)
              | exact resolve b19e274845 b19e271093
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e271093 b19e274845
            have b19e306865 : (M.op x y) = (M.op y (M.op y (k y y))) ∨ y = (M.op y y) := by grind
            clear b19e306479
            have b19e306956 : x = (M.op y (M.op y (k y y))) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e306865
                 have i₂ := b19e77
                 grind)
              | exact superpose b19e77 b19e306865
              | exact resolve b19e306865 b19e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e306865
            have b19e318704 : ∀ X0 X1 X2 : G, (M.op X0 (σ X1)) = (M.op (M.op X2 (σ X1)) X0) ∨ (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e1249 X0 (τ X0) X2
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e1249
              | exact resolve b19e1249 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1249
            have b19e319106 : ∀ X0 X1 X2 : G, (M.op X0 (σ X1)) = (M.op (M.op X2 (σ X1)) X0) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e318704 X0 X1 X2
                 have i₂ := b19e31 X0 X1
                 grind)
              | exact superpose b19e31 b19e318704
              | (have j0 := b19e318704 X0 X1 X2
                 grind)
              | exact resolve b19e318704 b19e31
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e31 b19e318704
            have b19e363304 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e17 (σ X1) (σ X0)
                 have i₂ := b19e1268 X1 X0
                 grind)
              | exact superpose b19e1268 b19e17
              | (have j0 := b19e17 (σ X1) (σ X0)
                 have j1 := b19e1268 X1 X0
                 grind)
              | (have r₁ := b19e17 (σ X0) (σ X1)
                 have r₂ := b19e1268 X0 X1
                 grind)
              | exact resolve b19e17 b19e1268
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1268
            have b19e363558 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have j0 := b19e363304 X0 X1
                 have j1 := b19e17 (σ X1) (σ X0)
                 grind)
              | (have r₁ := b19e363304 X0 X1
                 have r₂ := b19e17 (σ X1) (σ X0)
                 grind)
              | exact resolve b19e363304 b19e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e363304
            have b19e363571 : ∀ X0 X1 : G, (σ X1) = (σ (k X1 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have i₁ := b19e363558 X0 X1
                 have i₂ := b19e20 X1 X0
                 grind)
              | exact superpose b19e20 b19e363558
              | (have j0 := b19e363558 X0 X1
                 grind)
              | exact resolve b19e363558 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e363558
            have b19e363572 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
              intro X0 X1
              first
              | (have j0 := b19e363571 X0 X1
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e363571
            have b19e468550 : ∀ X0 X1 : G, (k (k X1 X1) X0) = (k (M.op X1 X1) X0) ∨ (M.op X1 X1) = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e29003 X0 (σ X0)
                 have i₂ := b19e15 X0
                 grind)
              | exact superpose b19e15 b19e29003
              | (have j0 := b19e29003 X1 X1
                 grind)
              | exact resolve b19e29003 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e29003
            have b19e487073 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e363572 (τ X0) (τ X1)
                 have i₂ := b19e1307 X1 X0
                 grind)
              | exact superpose b19e1307 b19e363572
              | (have j0 := b19e363572 (τ X0) (τ X1)
                 grind)
              | exact resolve b19e363572 b19e1307
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1307 b19e363572
            have b19e487088 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e487073 X0 X1
                 have i₂ := b19e16 (k X0 X1)
                 grind)
              | exact superpose b19e16 b19e487073
              | (have j0 := b19e487073 X0 X1
                 grind)
              | exact resolve b19e487073 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487073
            have b19e487092 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e487088 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e487088
              | (have j0 := b19e487088 X0 X1
                 grind)
              | exact resolve b19e487088 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487088
            have b19e487095 : ∀ X0 X1 : G, (σ (τ X1)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e487092 X0 X1
                 have i₂ := b19e32 X0 (τ X1)
                 grind)
              | exact superpose b19e32 b19e487092
              | (have j0 := b19e487092 X0 X1
                 grind)
              | exact resolve b19e487092 b19e32
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e32 b19e487092
            have b19e487096 : ∀ X0 X1 : G, (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (σ (τ X1)) := by
              intro X0 X1
              first
              | (have i₁ := b19e487095 X0 X0
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e487095
              | (have j0 := b19e487095 X0 X1
                 grind)
              | exact resolve b19e487095 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487095
            have b19e487097 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
              intro X0 X1
              first
              | (have i₁ := b19e487096 X0 X1
                 have i₂ := b19e16 X1
                 grind)
              | exact superpose b19e16 b19e487096
              | (have j0 := b19e487096 X0 X1
                 grind)
              | exact resolve b19e487096 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487096
            have b19e487098 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e487097 X0 X1
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e487097
              | (have j0 := b19e487097 X0 X1
                 grind)
              | exact resolve b19e487097 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487097
            have b19e487102 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have i₁ := b19e487098 X0 (M.op X0 (M.op X0 X0))
                 have i₂ := b19e15139 X0
                 grind)
              | exact superpose b19e15139 b19e487098
              | (have j0 := b19e487098 X0 (M.op X0 (M.op X0 X0))
                 grind)
              | (have r₁ := b19e487098 X0 (M.op X0 (M.op X0 X0))
                 have r₂ := b19e15139 X0
                 grind)
              | exact resolve b19e487098 b19e15139
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487098
            have b19e487121 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) ∨ (M.op X0 (M.op X0 X0)) = X0 := by
              intro X0
              first
              | (have j0 := b19e487102 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e487102
            have b19e487130 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X0) := by
              intro X0
              first
              | (have j0 := b19e487121 X0
                 have j1 := b19e3283 X0 X0
                 grind)
              | (have r₁ := b19e487121 x
                 have r₂ := b19e3283 x x
                 grind)
              | exact resolve b19e487121 b19e3283
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e3283 b19e487121
            have b19e487917 : (M.op (σ y) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) := by
              first
              | (have i₁ := b19e487130 (σ y)
                 have i₂ := b19e597 (σ y)
                 grind)
              | exact superpose b19e597 b19e487130
              | exact resolve b19e487130 b19e597
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e597 b19e487130
            have b19e488965 : (τ (M.op (σ y) (σ y))) = (k (τ (M.op (σ y) (σ y))) y) := by
              first
              | (have i₁ := b19e51 (M.op (σ y) (σ y)) y
                 have i₂ := b19e487917
                 grind)
              | exact superpose b19e487917 b19e51
              | exact resolve b19e51 b19e487917
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e51 b19e487917
            have b19e493133 : (k y y) = (k (k y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b19e488965
                 have i₂ := b19e1319 y
                 grind)
              | exact superpose b19e1319 b19e488965
              | (have j1 := b19e1319 y
                 grind)
              | exact resolve b19e488965 b19e1319
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e1319
            have b19e497977 : (M.op y y) = (k (M.op y y) y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
            clear b19e493133
            have b19e499727 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) (M.op (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e15139 (k X0 X0)
                 have i₂ := b19e183527 X0 (k X0 X0)
                 grind)
              | exact superpose b19e183527 b19e15139
              | (have j1 := b19e183527 X0 x
                 grind)
              | exact resolve b19e15139 b19e183527
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e15139 b19e183527
            have b19e503458 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op X0 (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have i₁ := b19e96886 X0 X0 x
                 have i₂ := b19e270714 X0 x
                 grind)
              | exact superpose b19e270714 b19e96886
              | (have j0 := b19e96886 X0 x x
                 have j1 := b19e270714 X0 x
                 grind)
              | exact resolve b19e96886 b19e270714
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e96886 b19e270714
            have b19e503569 : ∀ X0 : G, (M.op (k X0 X0) X0) = (M.op X0 (M.op X0 (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
              intro X0
              first
              | (have j0 := b19e503458 X0
                 grind)
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e503458
            have b19e524605 : x = (M.op (k y y) y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e306956
                 have i₂ := b19e503569 y
                 grind)
              | exact superpose b19e503569 b19e306956
              | (have j1 := b19e503569 y
                 grind)
              | exact resolve b19e306956 b19e503569
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e306956 b19e503569
            have b19e524647 : x = (M.op (k y y) y) ∨ y = (M.op y y) := by grind
            clear b19e524605
            have b19e639404 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
              intro X0 X1 X2
              first
              | (have i₁ := b19e319106 X0 (τ X0) X2
                 have i₂ := b19e16 X0
                 grind)
              | exact superpose b19e16 b19e319106
              | exact resolve b19e319106 b19e16
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e319106
            have b19e645634 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e14 X0 X1 x
                 have i₂ := b19e639404 X1 X0 x
                 grind)
              | exact superpose b19e639404 b19e14
              | (have j1 := b19e639404 X1 X0 x
                 grind)
              | exact resolve b19e14 b19e639404
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e639404
            have b19e647341 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) ∨ (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
              intro X0 X1
              first
              | (have i₁ := b19e324 X0 X1
                 have i₂ := b19e645634 X0 X1
                 grind)
              | exact superpose b19e645634 b19e324
              | (have j1 := b19e645634 X0 X1
                 grind)
              | exact resolve b19e324 b19e645634
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e324 b19e645634
            have b19e651877 : x = (M.op (k y y) x) ∨ x = (k (k y y) y) ∨ y = (k y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e647341 (k y y) y
                 have i₂ := b19e524647
                 grind)
              | exact superpose b19e524647 b19e647341
              | (have j0 := b19e647341 x (M.op (k y y) x)
                 grind)
              | exact resolve b19e647341 b19e524647
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e524647 b19e647341
            have b19e651939 : x = (k (k y y) y) ∨ x = (M.op (k y y) x) ∨ y = (k y y) := by
              first
              | (have j1 := b19e17 y y
                 grind)
              | (have r₁ := b19e651877
                 have r₂ := b19e17 y y
                 grind)
              | exact resolve b19e651877 b19e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e651877
            have b19e668472 : x = (k (M.op y y) y) ∨ x = (M.op (M.op y y) x) ∨ y = (M.op y y) ∨ y = (M.op y y) := by grind
            clear b19e651939
            have b19e668479 : x = (k (M.op y y) y) ∨ x = (M.op (M.op y y) x) ∨ y = (M.op y y) := by grind
            clear b19e668472
            have b19e668482 : x = (M.op x (M.op y x)) ∨ x = (k (M.op y y) y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e668479
                 have i₂ := b19e14 x y y
                 grind)
              | exact superpose b19e14 b19e668479
              | exact resolve b19e668479 b19e14
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e668479
            have b19e668483 : x = (M.op x x) ∨ x = (k (M.op y y) y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e668482
                 have i₂ := b19e79 x
                 grind)
              | exact superpose b19e79 b19e668482
              | exact resolve b19e668482 b19e79
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e668482
            have b19e668484 : x = (k (M.op y y) y) ∨ y = (M.op y y) := by
              first
              | (have r₁ := b19e668483
                 have r₂ := b19e25
                 grind)
              | exact resolve b19e668483 b19e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e668483
            have b19e688601 : (k y y) = (k (k y y) (M.op (k y y) x)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e499727 y
                 have i₂ := b19e275017
                 grind)
              | exact superpose b19e275017 b19e499727
              | (have j0 := b19e499727 y
                 grind)
              | exact resolve b19e499727 b19e275017
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e275017 b19e499727
            have b19e688605 : (k y y) = (k (k y y) (M.op (k y y) x)) ∨ y = (M.op y y) := by grind
            clear b19e688601
            have b19e688612 : (k y y) = (k (M.op y y) (M.op (k y y) x)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e468550 (M.op (k y y) x) y
                 have i₂ := b19e688605
                 grind)
              | exact superpose b19e688605 b19e468550
              | (have j0 := b19e468550 x y
                 grind)
              | exact resolve b19e468550 b19e688605
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e468550 b19e688605
            have b19e688613 : (k y y) = (k (M.op y y) (M.op (k y y) x)) ∨ y = (M.op y y) := by grind
            clear b19e688612
            have b19e781593 : x = (M.op y y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
              first
              | (have i₁ := b19e668484
                 have i₂ := b19e497977
                 grind)
              | exact superpose b19e497977 b19e668484
              | exact resolve b19e668484 b19e497977
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e497977 b19e668484
            have b19e781594 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
            clear b19e781593
            have b19e781600 : (τ (σ y)) = (k (τ (σ y)) y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b19e488965
                 have i₂ := b19e781594
                 grind)
              | exact superpose b19e781594 b19e488965
              | exact resolve b19e488965 b19e781594
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e488965 b19e781594
            have b19e781634 : y = (k y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b19e781600
                 have i₂ := b19e15 y
                 grind)
              | exact superpose b19e15 b19e781600
              | exact resolve b19e781600 b19e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e781600
            have b19e781640 : y = (k y y) ∨ x = (M.op y y) := by
              first
              | (have j1 := b19e17 y y
                 grind)
              | (have r₁ := b19e781634
                 have r₂ := b19e17 y y
                 grind)
              | exact resolve b19e781634 b19e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e781634
            have b19e781808 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b19e14801 y
                 have i₂ := b19e781640
                 grind)
              | exact superpose b19e781640 b19e14801
              | (have j0 := b19e14801 y
                 grind)
              | (have r₁ := b19e14801 y
                 have r₂ := b19e781640
                 grind)
              | exact resolve b19e14801 b19e781640
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e14801 b19e781640
            have b19e781981 : y = (M.op y y) ∨ x = (M.op y y) := by grind
            clear b19e781808
            have b19e782118 : (M.op x y) = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b19e79 y
                 have i₂ := b19e781981
                 grind)
              | exact superpose b19e781981 b19e79
              | exact resolve b19e79 b19e781981
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e79 b19e781981
            have b19e782788 : x = (M.op y y) ∨ x = (M.op y y) := by
              first
              | (have i₁ := b19e782118
                 have i₂ := b19e77
                 grind)
              | exact superpose b19e77 b19e782118
              | exact resolve b19e782118 b19e77
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e77 b19e782118
            have b19e782789 : x = (M.op y y) := by grind
            clear b19e782788
            have b19e782982 : (k y y) = (k x (M.op (k y y) x)) ∨ x = y := by
              first
              | (have i₁ := b19e688613
                 have i₂ := b19e782789
                 grind)
              | exact superpose b19e782789 b19e688613
              | exact resolve b19e688613 b19e782789
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e688613
            have b19e783811 : x = (k x (M.op (k y y) x)) ∨ x = y := by
              first
              | (have i₁ := b19e263892 y y
                 have i₂ := b19e782789
                 grind)
              | exact superpose b19e782789 b19e263892
              | exact resolve b19e263892 b19e782789
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e263892 b19e782789
            have b19e784211 : x = (k x (M.op (k y y) x)) := by
              first
              | (have r₁ := b19e783811
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e783811 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e783811
            have b19e784840 : (k y y) = (k x (M.op (k y y) x)) := by
              first
              | (have r₁ := b19e782982
                 have r₂ := b19e23
                 grind)
              | exact resolve b19e782982 b19e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e782982
            have b19e785409 : x = (k y y) := by
              first
              | (have i₁ := b19e784840
                 have i₂ := b19e784211
                 grind)
              | exact superpose b19e784211 b19e784840
              | exact resolve b19e784840 b19e784211
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e784211 b19e784840
            have b19e786566 : (σ y) = (k (σ y) (M.op (σ y) (σ x))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b19e16214 y
                 have i₂ := b19e785409
                 grind)
              | exact superpose b19e785409 b19e16214
              | (have j0 := b19e16214 y
                 grind)
              | exact resolve b19e16214 b19e785409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e16214
            have b19e787038 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
              first
              | (have i₁ := b19e786566
                 have i₂ := b19e24
                 grind)
              | exact superpose b19e24 b19e786566
              | exact resolve b19e786566 b19e24
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e786566
            have b19e787231 : (σ y) = (k (σ y) (σ y)) := by
              first
              | (have j1 := b19e17 (σ y) (σ y)
                 grind)
              | (have r₁ := b19e787038
                 have r₂ := b19e17 (σ y) (σ y)
                 grind)
              | exact resolve b19e787038 b19e17
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e787038
            have b19e787311 : (σ y) = (σ (k y y)) := by
              first
              | (have i₁ := b19e787231
                 have i₂ := b19e20 y y
                 grind)
              | exact superpose b19e20 b19e787231
              | exact resolve b19e787231 b19e20
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e787231
            have b19e787350 : (σ x) = (σ y) := by
              first
              | (have i₁ := b19e787311
                 have i₂ := b19e785409
                 grind)
              | exact superpose b19e785409 b19e787311
              | exact resolve b19e787311 b19e785409
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b19e785409 b19e787311
            have b19e787373 : False := by grind
            exact b19e787373
          · have b20e26 : x ≠ x := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h2a h2b
            have b20e28 : False := by grind
            exact b20e28
      · rcases eq_or_ne ((σ x)) ((σ y)) with h1b | h1b
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b21e15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
              intro X0
              grind
            have b21e23 : x ≠ y := by grind
            have b21e25 : (σ x) = (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b21e30 : y = (τ (σ x)) := by
              first
              | (have i₁ := b21e15 y
                 have i₂ := b21e25
                 grind)
              | exact superpose b21e25 b21e15
              | exact resolve b21e15 b21e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            have b21e31 : x = y := by
              first
              | (have i₁ := b21e30
                 have i₂ := b21e15 x
                 grind)
              | exact superpose b21e15 b21e30
              | exact resolve b21e30 b21e15
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b21e30
            have b21e32 : False := by grind
            exact b21e32
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b22e16 : ∀ X0 : G, (τ (σ X0)) = X0 := by
                intro X0
                grind
              have b22e24 : x ≠ y := by grind
              have b22e26 : (σ x) = (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b22e32 : y = (τ (σ x)) := by
                first
                | (have i₁ := b22e16 y
                   have i₂ := b22e26
                   grind)
                | exact superpose b22e26 b22e16
                | exact resolve b22e16 b22e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              have b22e33 : x = y := by
                first
                | (have i₁ := b22e32
                   have i₂ := b22e16 x
                   grind)
                | exact superpose b22e16 b22e32
                | exact resolve b22e32 b22e16
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b22e32
              have b22e34 : False := by grind
              exact b22e34
            · have b23e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b23e30 : False := by grind
              exact b23e30
        · rcases eq_or_ne (M.op x x) (x) with h2a | h2a
          · have b24e19 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
              intro X0 X1
              grind
            have b24e20 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
              intro X0 X1
              grind
            have b24e21 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
            have b24e22 : y ≠ (M.op y x) := by grind
            have b24e23 : x ≠ y := by grind
            have b24e24 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
            have b24e25 : (σ x) ≠ (σ y) := by grind
            clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a
            have b24e67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
            have b24e1628 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
              first
              | (have i₁ := b24e24
                 have i₂ := b24e67 x y
                 grind)
              | exact superpose b24e67 b24e24
              | (have j1 := b24e67 x y
                 grind)
              | (have r₁ := b24e24
                 have r₂ := b24e67 x y
                 grind)
              | exact resolve b24e24 b24e67
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e67
            have b24e1652 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
            clear b24e1628
            have b24e1657 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
              first
              | (have r₁ := b24e1652
                 have r₂ := b24e25
                 grind)
              | exact resolve b24e1652 b24e25
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1652
            have b24e1666 : (σ (M.op x y)) ≠ (σ (k x y)) := by
              first
              | (have i₁ := b24e21
                 have i₂ := b24e1657
                 grind)
              | exact superpose b24e1657 b24e21
              | exact resolve b24e21 b24e1657
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1657
            have b24e1857 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
              first
              | (have i₁ := b24e1666
                 have i₂ := b24e19 x y
                 grind)
              | exact superpose b24e19 b24e1666
              | (have j1 := b24e19 x y
                 grind)
              | (have r₁ := b24e1666
                 have r₂ := b24e19 (σ (M.op x y)) (σ (k x y))
                 grind)
              | (have r₁ := b24e1666
                 have r₂ := b24e19 (σ (k x y)) (σ (M.op x y))
                 grind)
              | exact resolve b24e1666 b24e19
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1666
            have b24e1858 : x = y ∨ y = (M.op y x) := by grind
            clear b24e1857
            have b24e1859 : y = (M.op y x) := by
              first
              | (have r₁ := b24e1858
                 have r₂ := b24e23
                 grind)
              | exact resolve b24e1858 b24e23
              | grind
              | grind (splits := 40)
              | grind (splits := 40) (ematch := 20)
            clear b24e1858
            have b24e1860 : False := by grind
            exact b24e1860
          · rcases eq_or_ne (x) (x) with h2b | h2b
            · have b25e20 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X1 := by
                intro X0 X1
                grind
              have b25e21 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
                intro X0 X1
                grind
              have b25e22 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
              have b25e23 : y ≠ (M.op y x) := by grind
              have b25e24 : x ≠ y := by grind
              have b25e25 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
              have b25e26 : (σ x) ≠ (σ y) := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b25e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
              have b25e1897 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
                first
                | (have i₁ := b25e25
                   have i₂ := b25e68 x y
                   grind)
                | exact superpose b25e68 b25e25
                | (have j1 := b25e68 x y
                   grind)
                | (have r₁ := b25e25
                   have r₂ := b25e68 x y
                   grind)
                | exact resolve b25e25 b25e68
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e68
              have b25e1929 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by grind
              clear b25e1897
              have b25e1936 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
                first
                | (have r₁ := b25e1929
                   have r₂ := b25e26
                   grind)
                | exact resolve b25e1929 b25e26
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1929
              have b25e1947 : (σ (M.op x y)) ≠ (σ (k x y)) := by
                first
                | (have i₁ := b25e22
                   have i₂ := b25e1936
                   grind)
                | exact superpose b25e1936 b25e22
                | exact resolve b25e22 b25e1936
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1936
              have b25e1976 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = y ∨ y = (M.op y x) := by
                first
                | (have i₁ := b25e1947
                   have i₂ := b25e20 x y
                   grind)
                | exact superpose b25e20 b25e1947
                | (have j1 := b25e20 x y
                   grind)
                | (have r₁ := b25e1947
                   have r₂ := b25e20 (σ (M.op x y)) (σ (k x y))
                   grind)
                | (have r₁ := b25e1947
                   have r₂ := b25e20 (σ (k x y)) (σ (M.op x y))
                   grind)
                | exact resolve b25e1947 b25e20
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1947
              have b25e1977 : x = y ∨ y = (M.op y x) := by grind
              clear b25e1976
              have b25e1978 : y = (M.op y x) := by
                first
                | (have r₁ := b25e1977
                   have r₂ := b25e24
                   grind)
                | exact resolve b25e1977 b25e24
                | grind
                | grind (splits := 40)
                | grind (splits := 40) (ematch := 20)
              clear b25e1977
              have b25e1979 : False := by grind
              exact b25e1979
            · have b26e28 : x ≠ x := by grind
              clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b h2a h2b
              have b26e30 : False := by grind
              exact b26e30
