import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4343`: `x ◇ (y ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation4343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4343.models_iff G M).mp hM
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
      have b0e229 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
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
      have b0e243 : False := by grind
      exact b0e243
    · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
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
        have b1e49 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e52
        have b1e55 : (M.op y y) = (k x y) := by grind
        clear b1e49
        have b1e56 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
          first
          | (have i₁ := b1e54
             have i₂ := b1e18 y y
             grind)
          | exact superpose b1e18 b1e54
          | exact resolve b1e54 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e54
        have b1e57 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e56
             have i₂ := b1e53 y
             grind)
          | exact superpose b1e53 b1e56
          | exact resolve b1e56 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e56
        have b1e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b1e18 X0 X0
             have i₂ := b1e53 (σ X0)
             grind)
          | exact superpose b1e53 b1e18
          | exact resolve b1e18 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b1e59 X0
             have i₂ := b1e53 X0
             grind)
          | exact superpose b1e53 b1e59
          | exact resolve b1e59 b1e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53 b1e59
        have b1e72 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e76 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b1e72 X0
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e72
          | (have j0 := b1e72 X0
             grind)
          | exact resolve b1e72 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e72
        have b1e137 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e23
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e23
          | exact resolve b1e23 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e23
        have b1e700 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e76 (σ x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e76
          | (have j0 := b1e76 (σ x)
             grind)
          | (have r₁ := b1e76 (σ x)
             have r₂ := b1e57
             grind)
          | exact resolve b1e76 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e76
        have b1e701 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e700
        have b1e702 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e701
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e701
          | exact resolve b1e701 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e701
        have b1e703 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e702
             have r₂ := b1e137
             grind)
          | exact resolve b1e702 b1e137
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e702
        have b1e704 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e703
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e703
          | exact resolve b1e703 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e703
        have b1e705 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e704
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e704
          | exact resolve b1e704 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e704
        have b1e706 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e705
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e705
          | exact resolve b1e705 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e705
        have b1e707 : False := by grind
        exact b1e707
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
        have b2e46 : (M.op x x) ≠ (M.op x x) ∨ (M.op y y) = (k x y) := by
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
        clear b2e46
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
        have b2e87 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
        have b2e149 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
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
        have b2e991 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e992 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e991
             have r₂ := b2e21
             grind)
          | exact resolve b2e991 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e991
        have b2e993 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e992
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e992
          | exact resolve b2e992 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e992
        have b2e994 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e993
             have i₂ := b2e50
             grind)
          | exact superpose b2e50 b2e993
          | exact resolve b2e993 b2e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e50 b2e993
        have b2e995 : False := by grind
        exact b2e995
  · rcases eq_or_ne (M.op x y) (M.op y y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) (M.op (σ x) (σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : (M.op x y) ≠ (M.op x x) := by grind
        have b3e21 : (M.op x y) = (M.op y y) := by grind
        have b3e22 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e52 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
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
        have b3e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b3e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e54 : (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
        clear b3e52
        have b3e56 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e54
             have i₂ := b3e18 x y
             grind)
          | exact superpose b3e18 b3e54
          | exact resolve b3e54 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e54
        have b3e72 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
        have b3e80 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e15 (σ y) (σ y)
             have i₂ := b3e56
             grind)
          | exact superpose b3e56 b3e15
          | exact resolve b3e15 b3e56
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e56
        have b3e81 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e80
        have b3e82 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e81
          | exact resolve b3e81 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81
        have b3e83 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e82
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e82
          | exact resolve b3e82 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e82
        have b3e84 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e83
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e83
          | exact resolve b3e83 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e83
        have b3e145 : (k x y) = (τ (σ (M.op x y))) := by
          first
          | (have i₁ := b3e13 (k x y)
             have i₂ := b3e84
             grind)
          | exact superpose b3e84 b3e13
          | exact resolve b3e13 b3e84
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e84
        have b3e146 : (M.op x y) = (k x y) := by
          first
          | (have i₁ := b3e145
             have i₂ := b3e13 (M.op x y)
             grind)
          | exact superpose b3e13 b3e145
          | exact resolve b3e145 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e145
        have b3e197 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e198 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e197
             have r₂ := b3e20
             grind)
          | exact resolve b3e197 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e197
        have b3e201 : (M.op x y) = (M.op x x) := by
          first
          | (have i₁ := b3e146
             have i₂ := b3e198
             grind)
          | exact superpose b3e198 b3e146
          | exact resolve b3e146 b3e198
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e146 b3e198
        have b3e206 : False := by grind
        exact b3e206
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
          have b4e69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e70 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b4e68
          have b4e72 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b4e70
               have i₂ := b4e19 y y
               grind)
            | exact superpose b4e19 b4e70
            | exact resolve b4e70 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e70
          have b4e74 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b4e72
               have i₂ := b4e69 y
               grind)
            | exact superpose b4e69 b4e72
            | exact resolve b4e72 b4e69
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e69 b4e72
          have b4e75 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e74
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e74
            | exact resolve b4e74 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e74
          have b4e76 : False := by grind
          exact b4e76
        · have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b5e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e65 (σ X0)
               grind)
            | exact superpose b5e65 b5e19
            | exact resolve b5e19 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e69 X0
               have i₂ := b5e65 X0
               grind)
            | exact superpose b5e65 b5e69
            | exact resolve b5e69 b5e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e65 b5e69
          have b5e86 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e130 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e236 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e86 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e86
          have b5e237 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e236
               have r₂ := b5e21
               grind)
            | exact resolve b5e236 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e236
          have b5e1385 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e130 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e130
          have b5e1386 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1385
               have r₂ := b5e23
               grind)
            | exact resolve b5e1385 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1385
          have b5e1387 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1386
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1386
            | exact resolve b5e1386 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1386
          have b5e1388 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1387
               have i₂ := b5e237
               grind)
            | exact superpose b5e237 b5e1387
            | exact resolve b5e1387 b5e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e237 b5e1387
          have b5e1391 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1388
               grind)
            | exact superpose b5e1388 b5e23
            | exact resolve b5e23 b5e1388
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1388
          have b5e1399 : False := by grind
          exact b5e1399
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
        have b6e73 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
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
        have b6e74 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e73
        have b6e75 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e74
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e74
          | exact resolve b6e74 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e76 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e75
             have i₂ := b6e49 y
             grind)
          | exact superpose b6e49 b6e75
          | exact resolve b6e75 b6e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e49 b6e75
        have b6e138 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e76
             grind)
          | exact superpose b6e76 b6e13
          | exact resolve b6e13 b6e76
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e76
        have b6e139 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e138
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e138
          | exact resolve b6e138 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e138
        have b6e159 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e139
             grind)
          | exact superpose b6e139 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e139
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e139
        have b6e160 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e159
        have b6e162 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e160
             have r₂ := b6e21
             grind)
          | exact resolve b6e160 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e160
        have b6e164 : False := by grind
        exact b6e164
      · rcases eq_or_ne (M.op (σ x) (σ y)) (M.op (σ y) (σ y)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
            first
            | (have i₁ := b7e16 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e16
            | exact resolve b7e16 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b7e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e66 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
          clear b7e64
          have b7e67 : (M.op (σ x) (σ y)) = (σ (k y y)) := by
            first
            | (have i₁ := b7e66
               have i₂ := b7e19 y y
               grind)
            | exact superpose b7e19 b7e66
            | exact resolve b7e66 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e66
          have b7e68 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e67
               have i₂ := b7e65 y
               grind)
            | exact superpose b7e65 b7e67
            | exact resolve b7e67 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67
          have b7e70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b7e19 X0 X0
               have i₂ := b7e65 (σ X0)
               grind)
            | exact superpose b7e65 b7e19
            | exact resolve b7e19 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b7e70 X0
               have i₂ := b7e65 X0
               grind)
            | exact superpose b7e65 b7e70
            | exact resolve b7e70 b7e65
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e65 b7e70
          have b7e87 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e91 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e87 X0
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e87
            | (have j0 := b7e87 X0
               grind)
            | exact resolve b7e87 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e92 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e23
            | exact resolve b7e23 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e96 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e92
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e92
            | exact resolve b7e92 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e115 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e139 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e115 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e760 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e91 (σ x)
               have i₂ := b7e68
               grind)
            | exact superpose b7e68 b7e91
            | (have j0 := b7e91 (σ x)
               grind)
            | (have r₁ := b7e91 (σ x)
               have r₂ := b7e68
               grind)
            | exact resolve b7e91 b7e68
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e68 b7e91
          have b7e761 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e760
          have b7e762 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e761
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e761
            | exact resolve b7e761 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e761
          have b7e763 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e762
               have r₂ := b7e96
               grind)
            | exact resolve b7e762 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e762
          have b7e764 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e763
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e763
            | exact resolve b7e763 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e763
          have b7e765 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e764
               have i₂ := b7e79 x
               grind)
            | exact superpose b7e79 b7e764
            | exact resolve b7e764 b7e79
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e79 b7e764
          have b7e767 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e765
               have i₂ := b7e139 x y
               grind)
            | exact superpose b7e139 b7e765
            | (have j1 := b7e139 x y
               grind)
            | exact resolve b7e765 b7e139
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e769 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e765
               grind)
            | exact superpose b7e765 b7e14
            | exact resolve b7e14 b7e765
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e765
          have b7e781 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e769
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e769
            | exact resolve b7e769 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e769
          have b7e783 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e767
               have r₂ := b7e96
               grind)
            | exact resolve b7e767 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96 b7e767
          have b7e786 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e783
               have r₂ := b7e22
               grind)
            | exact resolve b7e783 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e783
          have b7e787 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e786
               have i₂ := b7e781
               grind)
            | exact superpose b7e781 b7e786
            | exact resolve b7e786 b7e781
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e781 b7e786
          have b7e788 : False := by grind
          exact b7e788
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
          have b8e122 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1116 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e122 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e122
          have b8e1117 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1116
               have r₂ := b8e23
               grind)
            | exact resolve b8e1116 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1116
          have b8e1118 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1117
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1117
            | exact resolve b8e1117 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1117
          have b8e1123 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1118
               grind)
            | exact superpose b8e1118 b8e20
            | exact resolve b8e20 b8e1118
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1118
          have b8e1195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1123
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1123
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1123 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1123
          have b8e1196 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1195
          have b8e1198 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1196
               have r₂ := b8e21
               grind)
            | exact resolve b8e1196 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1196
          have b8e1201 : False := by grind
          exact b8e1201

/-- `Equation4381`: `x ◇ (x ◇ x) = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_x_x_pyy_pxy_Equation4381 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4381 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4381.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
        intro X0 X1
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
      have b0e16 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
      have b0e33 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e11 X0 X2
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e11 (σ x) x
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : ∀ X0 : G, (M.op x y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e11 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e43 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y (M.op x y)) := by
        intro X0
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e37 y
           grind)
        | exact superpose b0e37 b0e11
        | exact resolve b0e11 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e45 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
        intro X0
        first
        | (have i₁ := b0e43 X0
           have i₂ := b0e37 (M.op x y)
           grind)
        | exact superpose b0e37 b0e43
        | exact resolve b0e43 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43
      have b0e69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
      have b0e86 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
      clear b0e45
      have b0e98 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
      have b0e101 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (σ y) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e36 X1
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e36
        | exact resolve b0e36 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e105 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e18
           have i₂ := b0e36 X0
           grind)
        | exact superpose b0e36 b0e18
        | exact resolve b0e18 b0e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e194 : ∀ X0 : G, (σ y) = (k (σ y) (M.op (σ y) X0)) := by
        intro X0
        grind
      clear b0e101
      have b0e350 : ∀ X0 : G, (k y (τ (M.op (σ y) X0))) = (τ (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e98 y (M.op (σ y) X0)
           have i₂ := b0e194 X0
           grind)
        | exact superpose b0e194 b0e98
        | exact resolve b0e98 b0e194
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98 b0e194
      have b0e352 : ∀ X0 : G, y = (k y (τ (M.op (σ y) X0))) := by
        intro X0
        first
        | (have i₁ := b0e350 X0
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e350
        | exact resolve b0e350 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e350
      have b0e362 : ∀ X0 : G, y = (M.op y (τ (M.op (σ y) X0))) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e16 y (τ (M.op (σ y) X0))
           have i₂ := b0e352 X0
           grind)
        | exact superpose b0e352 b0e16
        | (have j0 := b0e16 y (τ (M.op (σ y) X0))
           grind)
        | exact resolve b0e16 b0e352
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e352
      have b0e363 : ∀ X0 : G, y = (M.op x y) ∨ (M.op y y) = (τ (M.op (σ y) X0)) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e362 X0
           have i₂ := b0e37 (τ (M.op (σ y) X0))
           grind)
        | exact superpose b0e37 b0e362
        | (have j0 := b0e362 X0
           grind)
        | exact resolve b0e362 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e362
      have b0e368 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e363 X0
           have i₂ := b0e37 y
           grind)
        | exact superpose b0e37 b0e363
        | exact resolve b0e363 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e363
      have b0e371 : ∀ X0 : G, y = (M.op x y) ∨ (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e368 X0
           have i₂ := b0e37 y
           grind)
        | exact superpose b0e37 b0e368
        | (have j0 := b0e368 X0
           grind)
        | exact resolve b0e368 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e368
      have b0e372 : ∀ X0 : G, (M.op x y) = (τ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have j0 := b0e371 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e371
      have b0e1802 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e69 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69
      have b0e1805 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e1802 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1802
      have b0e5216 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e1805 (M.op x y)
           have i₂ := b0e86
           grind)
        | exact superpose b0e86 b0e1805
        | (have j0 := b0e1805 (M.op x y)
           grind)
        | exact resolve b0e1805 b0e86
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e86 b0e1805
      have b0e5234 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
      clear b0e5216
      have b0e5401 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) X0) = (M.op (σ (M.op x y)) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e33 (σ (M.op x y)) X1 x
           have i₂ := b0e5234
           grind)
        | exact superpose b0e5234 b0e33
        | exact resolve b0e33 b0e5234
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e5664 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
        intro X0
        first
        | (have i₁ := b0e5234
           have i₂ := b0e5401 (σ (M.op x y)) X0
           grind)
        | (have i₁ := b0e5234
           have i₂ := b0e5401 X0 (σ (M.op x y))
           grind)
        | exact superpose b0e5401 b0e5234
        | exact resolve b0e5234 b0e5401
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5234 b0e5401
      have b0e6391 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ y) X0) ∨ y = (M.op x y) := by
        intro X0
        first
        | (have i₁ := b0e13 (M.op (σ y) X0)
           have i₂ := b0e372 X0
           grind)
        | exact superpose b0e372 b0e13
        | exact resolve b0e13 b0e372
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e372
      have b0e6399 : y = (M.op x y) := by
        first
        | (have r₁ := b0e6391 x
           have r₂ := b0e105 x
           grind)
        | exact resolve b0e6391 b0e105
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e6391
      have b0e6612 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e105 X0
           have i₂ := b0e6399
           grind)
        | exact superpose b0e6399 b0e105
        | exact resolve b0e105 b0e6399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e6616 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e5664 X0
           have i₂ := b0e6399
           grind)
        | exact superpose b0e6399 b0e5664
        | exact resolve b0e5664 b0e6399
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e5664 b0e6399
      have b0e6619 : False := by
        have f6619_12 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) X0) := by
          intro X0
          grind
        have f6619_13 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) := by
          intro X0
          grind
        have f6619_24 : False := by
          first
          | (have r₁ := f6619_12 x
             have r₂ := f6619_13 x
             grind)
          | exact resolve f6619_12 f6619_13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        exact f6619_24
      exact b0e6619
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e24 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e22
             grind)
          | exact superpose b1e22 b1e21
          | exact resolve b1e21 b1e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e26 : (σ x) = (k (σ x) (σ x)) := by grind
        have b1e27 : (σ x) = (σ (k x x)) := by
          first
          | (have i₁ := b1e26
             have i₂ := b1e18 x x
             grind)
          | exact superpose b1e18 b1e26
          | exact resolve b1e26 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26
        have b1e32 : (k x x) = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 (k x x)
             have i₂ := b1e27
             grind)
          | exact superpose b1e27 b1e13
          | exact resolve b1e13 b1e27
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e27
        have b1e33 : x = (k x x) := by
          first
          | (have i₁ := b1e32
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e32
          | exact resolve b1e32 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e32
        have b1e84 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b1e33
             have i₂ := b1e17 x x
             grind)
          | exact superpose b1e17 b1e33
          | (have j1 := b1e17 x x
             grind)
          | exact resolve b1e33 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e33
        have b1e90 : x = (M.op x x) := by grind
        clear b1e84
        have b1e99 : x = y := by
          first
          | (have i₁ := b1e20
             have i₂ := b1e90
             grind)
          | exact superpose b1e90 b1e20
          | exact resolve b1e20 b1e90
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e90
        have b1e116 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e99
             grind)
          | exact superpose b1e99 b1e24
          | exact resolve b1e24 b1e99
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e99
        have b1e117 : False := by grind
        exact b1e117
      · have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e54 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e21
             have i₂ := b2e17 (σ x) X0
             grind)
          | (have i₁ := b2e21
             have i₂ := b2e17 X0 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e17 b2e21
          | (have j1 := b2e17 (σ x) (σ x)
             grind)
          | (have r₁ := b2e21
             have r₂ := b2e17 (σ x) (σ y)
             grind)
          | exact resolve b2e21 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e59 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e17 (σ x) X0
             grind)
          | exact superpose b2e17 b2e22
          | (have j1 := b2e17 (σ x) X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) (σ x)
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e17 (σ x) x
             grind)
          | exact resolve b2e22 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e66 : ∀ X0 : G, (M.op (σ x) (σ x)) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e59 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e59
        have b2e69 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have j0 := b2e54 X0
             grind)
          | (have r₁ := b2e54 X0
             have r₂ := b2e22
             grind)
          | exact resolve b2e54 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54
        have b2e265 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e69 (σ y)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e69
        have b2e266 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e265
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e265
          | exact resolve b2e265 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e265
        have b2e267 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e266
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e266
          | exact resolve b2e266 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e266
        have b2e296 : ∀ X0 : G, (σ x) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
          intro X0
          first
          | (have i₁ := b2e22
             have i₂ := b2e66 X0
             grind)
          | (have i₁ := b2e22
             have i₂ := b2e66 (M.op (σ x) (σ x))
             grind)
          | exact superpose b2e66 b2e22
          | (have j1 := b2e66 X0
             grind)
          | (have r₁ := b2e22
             have r₂ := b2e66 (σ x)
             grind)
          | exact resolve b2e22 b2e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e66
        have b2e1462 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) := by
          first
          | (have j0 := b2e296 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e296
        have b2e1463 : (M.op (σ x) (σ x)) = (σ (k x x)) := by
          first
          | (have i₁ := b2e1462
             have i₂ := b2e18 x x
             grind)
          | exact superpose b2e18 b2e1462
          | exact resolve b2e1462 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1462
        have b2e1622 : (σ y) ≠ (σ (k x x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e1463
             grind)
          | exact superpose b2e1463 b2e21
          | exact resolve b2e21 b2e1463
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1463
        have b2e2007 : (σ y) ≠ (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e1622
             have i₂ := b2e17 x x
             grind)
          | exact superpose b2e17 b2e1622
          | (have j1 := b2e17 x x
             grind)
          | exact resolve b2e1622 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1622
        have b2e2015 : (σ y) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by grind
        clear b2e2007
        have b2e2028 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
          first
          | (have i₁ := b2e2015
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e2015
          | exact resolve b2e2015 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2015
        have b2e2029 : x = (M.op x x) := by grind
        clear b2e2028
        have b2e2238 : x = y := by
          first
          | (have i₁ := b2e20
             have i₂ := b2e2029
             grind)
          | exact superpose b2e2029 b2e20
          | exact resolve b2e20 b2e2029
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e2029
        have b2e2307 : (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e267
             have i₂ := b2e2238
             grind)
          | exact superpose b2e2238 b2e267
          | exact resolve b2e267 b2e2238
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e267 b2e2238
        have b2e2312 : False := by grind
        exact b2e2312
  · rcases eq_or_ne (M.op x x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op x x) := by grind
        have b3e21 : x = (M.op x x) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : x ≠ y := by
          first
          | (have i₁ := b3e20
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e20
          | exact resolve b3e20 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
        have b3e57 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
          intro X0
          grind
        clear b3e28
        have b3e61 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
          intro X0
          first
          | (have i₁ := b3e57 X0
             have i₂ := b3e14 X0
             grind)
          | exact superpose b3e14 b3e57
          | exact resolve b3e57 b3e14
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e57
        have b3e67 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = X0 ∨ (σ x) = (σ y) := by
          intro X0
          first
          | (have i₁ := b3e17 (σ x) x
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e17
          | (have j0 := b3e17 (σ x) X0
             grind)
          | exact resolve b3e17 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e912 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e67 (σ (M.op (τ (σ x)) (τ (σ x))))
             have i₂ := b3e61 (σ x)
             grind)
          | exact superpose b3e61 b3e67
          | (have j0 := b3e67 (σ (M.op (τ (σ x)) (τ (σ x))))
             grind)
          | exact resolve b3e67 b3e61
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e61 b3e67
        have b3e915 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e912
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e912
          | exact resolve b3e912 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e912
        have b3e927 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e915
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e915
          | exact resolve b3e915 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e915
        have b3e930 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e927
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e927
          | exact resolve b3e927 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e927
        have b3e931 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by grind
        clear b3e930
        have b3e934 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e931
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e931
          | exact resolve b3e931 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e931
        have b3e936 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b3e934
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e934
          | exact resolve b3e934 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e934
        have b3e937 : (σ x) = (σ y) := by grind
        clear b3e936
        have b3e1179 : y = (τ (σ x)) := by
          first
          | (have i₁ := b3e13 y
             have i₂ := b3e937
             grind)
          | exact superpose b3e937 b3e13
          | exact resolve b3e13 b3e937
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e937
        have b3e1181 : x = y := by
          first
          | (have i₁ := b3e1179
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e1179
          | exact resolve b3e1179 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e1179
        have b3e1187 : False := by grind
        exact b3e1187
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x x) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e42 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e13 (σ x) x
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : ∀ X0 : G, (M.op x x) = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e47 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b4e43 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e43
            | exact resolve b4e43 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e48 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b4e42 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e42
            | exact resolve b4e42 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e62 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 (σ y)
               grind)
            | exact superpose b4e48 b4e20
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e71 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e62
               have i₂ := b4e47 y
               grind)
            | exact superpose b4e47 b4e62
            | exact resolve b4e62 b4e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e47 b4e62
          have b4e72 : False := by grind
          exact b4e72
        · have b5e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b5e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b5e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op x x) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e28 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
          have b5e31 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
            intro X0
            grind
          clear b5e28
          have b5e35 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
            intro X0
            first
            | (have i₁ := b5e31 X0
               have i₂ := b5e15 X0
               grind)
            | exact superpose b5e15 b5e31
            | exact resolve b5e31 b5e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e78 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 (σ x) X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ x)
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) x
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e87 : ∀ X0 : G, (M.op (σ x) (σ x)) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b5e78 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e78
          have b5e296 : (σ x) = (M.op (σ x) (σ (M.op (τ (σ x)) (τ (σ x))))) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
            first
            | (have i₁ := b5e35 (σ x)
               have i₂ := b5e87 (σ (M.op (τ (σ x)) (τ (σ x))))
               grind)
            | exact superpose b5e87 b5e35
            | (have j1 := b5e87 (σ (M.op (τ (σ x)) (τ (σ x))))
               grind)
            | exact resolve b5e35 b5e87
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e87
          have b5e298 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
            first
            | (have i₁ := b5e296
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e296
            | exact resolve b5e296 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e296
          have b5e301 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
            first
            | (have i₁ := b5e298
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e298
            | exact resolve b5e298 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e298
          have b5e303 : (M.op (σ x) (σ x)) = (σ (M.op (τ (σ x)) (τ (σ x)))) := by
            first
            | (have r₁ := b5e301
               have r₂ := b5e24
               grind)
            | exact resolve b5e301 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e301
          have b5e305 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e303
               have i₂ := b5e14 x
               grind)
            | exact superpose b5e14 b5e303
            | exact resolve b5e303 b5e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e303
          have b5e307 : (σ x) = (M.op (σ x) (σ x)) := by
            first
            | (have i₁ := b5e305
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e305
            | exact resolve b5e305 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e305
          have b5e309 : False := by grind
          exact b5e309
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
          intro X0 X1
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x x) := by grind
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
        have b6e42 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e12 (σ x) x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e61 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e19
             have i₂ := b6e42 X0
             grind)
          | exact superpose b6e42 b6e19
          | exact resolve b6e19 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
        have b6e95 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
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
        have b6e99 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x x) := by
          first
          | (have r₁ := b6e95
             have r₂ := b6e20
             grind)
          | exact resolve b6e95 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e95
        have b6e110 : (σ (M.op x y)) = (σ x) := by
          first
          | (have r₁ := b6e99
             have r₂ := b6e21
             grind)
          | exact resolve b6e99 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e99
        have b6e267 : ∀ X0 : G, (σ x) ≠ (M.op (σ y) X0) := by
          intro X0
          first
          | (have i₁ := b6e61 X0
             have i₂ := b6e110
             grind)
          | exact superpose b6e110 b6e61
          | exact resolve b6e61 b6e110
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e61 b6e110
        have b6e282 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b6e267 x
             have i₂ := b6e42 x
             grind)
          | exact superpose b6e42 b6e267
          | exact resolve b6e267 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e267
        have b6e1319 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e92 x x
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e92
          | exact resolve b6e92 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e92
        have b6e1509 : (σ y) = (σ (k x x)) ∨ (σ x) = (σ y) := by grind
        clear b6e1319
        have b6e1891 : (k x x) = (τ (σ y)) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e13 (k x x)
             have i₂ := b6e1509
             grind)
          | exact superpose b6e1509 b6e13
          | exact resolve b6e13 b6e1509
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1509
        have b6e1911 : y = (k x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e1891
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e1891
          | exact resolve b6e1891 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1891
        have b6e1941 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have i₁ := b6e17 x x
             have i₂ := b6e1911
             grind)
          | exact superpose b6e1911 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e1911
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1911
        have b6e1949 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
        clear b6e1941
        have b6e1958 : x = (M.op x x) ∨ (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1949
             have r₂ := b6e20
             grind)
          | exact resolve b6e1949 b6e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1949
        have b6e1976 : (σ x) = (σ y) := by
          first
          | (have r₁ := b6e1958
             have r₂ := b6e21
             grind)
          | exact resolve b6e1958 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e1958
        have b6e2094 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b6e282
             have i₂ := b6e1976
             grind)
          | exact superpose b6e1976 b6e282
          | exact resolve b6e282 b6e1976
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e282
        have b6e2118 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b6e2094
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e2094
          | exact resolve b6e2094 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e2094
        have b6e2125 : False := by grind
        exact b6e2125
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op x x) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e27 : (σ x) = (k (σ x) (σ x)) := by grind
          have b7e28 : (σ x) = (σ (k x x)) := by
            first
            | (have i₁ := b7e27
               have i₂ := b7e19 x x
               grind)
            | exact superpose b7e19 b7e27
            | exact resolve b7e27 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e27
          have b7e33 : (k x x) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x x)
               have i₂ := b7e28
               grind)
            | exact superpose b7e28 b7e14
            | exact resolve b7e14 b7e28
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e28
          have b7e34 : x = (k x x) := by
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
          have b7e78 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b7e34
               have i₂ := b7e18 x x
               grind)
            | exact superpose b7e18 b7e34
            | (have j1 := b7e18 x x
               grind)
            | exact resolve b7e34 b7e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e83 : x = (M.op x x) := by grind
          clear b7e78
          have b7e87 : False := by grind
          exact b7e87
        · have b8e18 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e61 : ∀ X0 : G, (σ y) ≠ X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e23
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e23
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e23
            | (have j1 := b8e18 (σ x) (σ x)
               grind)
            | (have r₁ := b8e23
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e23 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e76 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have j0 := b8e61 X0
               grind)
            | (have r₁ := b8e61 X0
               have r₂ := b8e24
               grind)
            | exact resolve b8e61 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e225 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e76 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e226 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e225
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e225
            | exact resolve b8e225 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e225
          have b8e227 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e226
               grind)
            | exact superpose b8e226 b8e20
            | exact resolve b8e20 b8e226
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e226
          have b8e229 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e227
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e227
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e227 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e227
          have b8e230 : y = (M.op x x) ∨ x = (M.op x x) := by grind
          clear b8e229
          have b8e231 : x = (M.op x x) := by
            first
            | (have r₁ := b8e230
               have r₂ := b8e21
               grind)
            | exact resolve b8e230 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e230
          have b8e232 : False := by grind
          exact b8e232

/-- `Equation4386`: `x ◇ (x ◇ x) = (y ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pyx_Equation4386 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4386 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4386.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
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
      have b0e70 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e75 : False := by grind
      exact b0e75
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e34 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X1 X2
               have i₂ := b4e13 X1 X0
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e35 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X1 (M.op X1 X0)
               have i₂ := b4e13 X0 X1
               grind)
            | exact superpose b4e13 b4e13
            | exact resolve b4e13 b4e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e37 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e38 : (M.op x (M.op x x)) = (M.op (M.op x y) y) := by
            first
            | (have i₁ := b4e13 x y
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e13
            | exact resolve b4e13 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e39 : (M.op x y) = (M.op (M.op x y) y) := by
            first
            | (have i₁ := b4e38
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e38
            | exact resolve b4e38 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e38
          have b4e49 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b4e51 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ X0 = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b4e56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 ∨ (k X1 X0) = X0 := by
            intro X0 X1
            first
            | (have j0 := b4e51 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51
          have b4e57 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e49 X0 X1
               have i₂ := b4e31 X1
               grind)
            | exact superpose b4e31 b4e49
            | (have j0 := b4e49 X0 X1
               grind)
            | exact resolve b4e49 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49
          have b4e59 : (M.op y (M.op y y)) = (M.op (M.op x y) (M.op x y)) := by
            first
            | (have i₁ := b4e13 y (M.op x y)
               have i₂ := b4e39
               grind)
            | exact superpose b4e39 b4e13
            | exact resolve b4e13 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op (M.op (M.op X0 X1) X0) (M.op X3 X1)) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b4e34 X2 X3 (M.op X3 X1)
               have i₂ := b4e34 X3 X1 X0
               grind)
            | (have i₁ := b4e34 X2 X3 (M.op X3 X1)
               have i₂ := b4e34 X0 X1 X3
               grind)
            | exact superpose b4e34 b4e34
            | exact resolve b4e34 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e125 : ∀ X0 X1 : G, (M.op (M.op X1 (σ X0)) X1) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e34 X1 (σ X0) (σ X0)
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e34
            | exact resolve b4e34 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e134 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X0) (M.op X2 X1)) = (M.op X2 (M.op X2 X2)) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e13 X2 (M.op X2 X1)
               have i₂ := b4e34 X2 X1 X0
               grind)
            | (have i₁ := b4e13 X2 (M.op X2 X1)
               have i₂ := b4e34 X0 X1 X2
               grind)
            | exact superpose b4e34 b4e13
            | exact resolve b4e13 b4e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e237 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 x)) := by
            intro X0
            first
            | (have i₁ := b4e35 x X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e35
            | exact resolve b4e35 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e35
          have b4e303 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op (M.op x y) (M.op X0 x)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 X0 X1
               have i₂ := b4e237 X0
               grind)
            | exact superpose b4e237 b4e13
            | exact resolve b4e13 b4e237
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e237
          have b4e327 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            first
            | (have j0 := b4e56 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e338 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y (M.op x y)) := by
            first
            | (have i₁ := b4e327 y (M.op x y)
               have i₂ := b4e39
               grind)
            | exact superpose b4e39 b4e327
            | (have j0 := b4e327 y (M.op x y)
               grind)
            | (have r₁ := b4e327 y (M.op x y)
               have r₂ := b4e39
               grind)
            | exact resolve b4e327 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e327
          have b4e343 : (M.op x y) = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
          clear b4e338
          have b4e577 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e57 x y
               grind)
            | exact superpose b4e57 b4e20
            | (have j1 := b4e57 x y
               grind)
            | exact resolve b4e20 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e582 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (σ X0)) X2) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e34 X2 (σ X0) (σ X1)
               have i₂ := b4e57 X1 X0
               grind)
            | exact superpose b4e57 b4e34
            | (have j1 := b4e57 X1 X0
               grind)
            | exact resolve b4e34 b4e57
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e34 b4e57
          have b4e631 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b4e577
               have r₂ := b4e23
               grind)
            | exact resolve b4e577 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e577
          have b4e3823 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b4e631
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e631
            | (have j1 := b4e18 y x
               grind)
            | (have r₁ := b4e631
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e631
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e631 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e631
          have b4e3825 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b4e3823
          have b4e3830 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b4e3825
               have r₂ := b4e21
               grind)
            | exact resolve b4e3825 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3825
          have b4e3838 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e14 (M.op y y)
               have i₂ := b4e3830
               grind)
            | exact superpose b4e3830 b4e14
            | exact resolve b4e14 b4e3830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3830
          have b4e3879 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b4e3838
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e3838
            | exact resolve b4e3838 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3838
          have b4e3880 : x = (M.op y y) := by grind
          clear b4e3879
          have b4e3908 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ y)) X0) := by
            intro X0
            first
            | (have i₁ := b4e125 y X0
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e125
            | exact resolve b4e125 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e125
          have b4e3917 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) (M.op X1 y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e121 y y X0 X1
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e121
            | exact resolve b4e121 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e3920 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op x y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e134 y y X0
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e134
            | exact resolve b4e134 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e134
          have b4e5185 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 x)) = (M.op (M.op x y) (M.op X0 y)) := by
            intro X0
            first
            | (have i₁ := b4e303 X0 x
               have i₂ := b4e3917 x X0
               grind)
            | exact superpose b4e3917 b4e303
            | exact resolve b4e303 b4e3917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e303 b4e3917
          have b4e53389 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e582 y (M.op x y) X0
               have i₂ := b4e343
               grind)
            | exact superpose b4e343 b4e582
            | (have j0 := b4e582 y (M.op x y) x
               grind)
            | exact resolve b4e582 b4e343
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e343 b4e582
          have b4e54056 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e53389 X0
               have i₂ := b4e31 (M.op x y)
               grind)
            | exact superpose b4e31 b4e53389
            | exact resolve b4e53389 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e53389
          have b4e54233 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op y (M.op y y))) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e54056 X0
               have i₂ := b4e59
               grind)
            | exact superpose b4e59 b4e54056
            | exact resolve b4e54056 b4e59
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e59 b4e54056
          have b4e54298 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (σ (M.op y x)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e54233 X0
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e54233
            | exact resolve b4e54233 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54233
          have b4e54316 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) X0) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b4e54298 X0
               have i₂ := b4e37
               grind)
            | exact superpose b4e37 b4e54298
            | exact resolve b4e54298 b4e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37 b4e54298
          have b4e54322 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e54316 x
               have i₂ := b4e3908 x
               grind)
            | exact superpose b4e3908 b4e54316
            | exact resolve b4e54316 b4e3908
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3908 b4e54316
          have b4e54324 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e54322
               have r₂ := b4e20
               grind)
            | exact resolve b4e54322 b4e20
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54322
          have b4e54326 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e54324
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e54324
            | exact resolve b4e54324 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54324
          have b4e220881 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e54326
               grind)
            | exact superpose b4e54326 b4e14
            | exact resolve b4e14 b4e54326
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54326
          have b4e220883 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e220881
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e220881
            | exact resolve b4e220881 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e220881
          have b4e220884 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
          clear b4e220883
          have b4e220898 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (M.op x y)
               have i₂ := b4e220884
               grind)
            | exact superpose b4e220884 b4e14
            | exact resolve b4e14 b4e220884
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e220884
          have b4e220938 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e220898
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e220898
            | exact resolve b4e220898 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e220898
          have b4e221109 : (M.op x (M.op x x)) = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e3920 x
               have i₂ := b4e220938
               grind)
            | exact superpose b4e220938 b4e3920
            | exact resolve b4e3920 b4e220938
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3920 b4e220938
          have b4e221329 : x = (M.op x (M.op x x)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e221109
               have i₂ := b4e3880
               grind)
            | exact superpose b4e3880 b4e221109
            | exact resolve b4e221109 b4e3880
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3880 b4e221109
          have b4e221425 : x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e221329
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e221329
            | exact resolve b4e221329 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e221329
          have b4e221426 : x = (M.op x y) := by grind
          clear b4e221425
          have b4e221677 : (M.op x x) = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e5185 x
               have i₂ := b4e221426
               grind)
            | exact superpose b4e221426 b4e5185
            | exact resolve b4e5185 b4e221426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5185
          have b4e222025 : y = (M.op x y) := by
            first
            | (have i₁ := b4e221677
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e221677
            | exact resolve b4e221677 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e221677
          have b4e222221 : x = y := by
            first
            | (have i₁ := b4e222025
               have i₂ := b4e221426
               grind)
            | exact superpose b4e221426 b4e222025
            | exact resolve b4e222025 b4e221426
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e221426 b4e222025
          have b4e222370 : False := by grind
          exact b4e222370
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
          have b5e79 : (σ y) ≠ (σ (M.op x x)) := by
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
          have b5e85 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e79
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e79
            | exact resolve b5e79 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e79
          have b5e86 : False := by grind
          exact b5e86
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
          have b7e96 : (σ y) = (σ (M.op x x)) := by
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
          have b7e144 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e96
               grind)
            | exact superpose b7e96 b7e14
            | exact resolve b7e14 b7e96
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e96
          have b7e145 : y = (M.op x x) := by
            first
            | (have i₁ := b7e144
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e144
            | exact resolve b7e144 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e144
          have b7e149 : False := by grind
          exact b7e149
        · have b8e13 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X0) X1) := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e58 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e63 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 (σ x)) = (k (σ x) X0) ∨ (σ x) = X0 := by
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
          have b8e66 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e58 X0 X1
               have i₂ := b8e31 X1
               grind)
            | exact superpose b8e31 b8e58
            | (have j0 := b8e58 X0 X1
               grind)
            | exact resolve b8e58 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e58
          have b8e76 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b8e13 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31
          have b8e219 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e63 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e63
          have b8e220 : (M.op (σ y) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e219
               have r₂ := b8e23
               grind)
            | exact resolve b8e219 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e219
          have b8e221 : (M.op (σ y) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e220
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e220
            | exact resolve b8e220 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e220
          have b8e330 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e66 x y
               grind)
            | exact superpose b8e66 b8e20
            | (have j1 := b8e66 x y
               grind)
            | exact resolve b8e20 b8e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e66
          have b8e378 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
            first
            | (have r₁ := b8e330
               have r₂ := b8e23
               grind)
            | exact resolve b8e330 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e330
          have b8e2020 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by
            first
            | (have i₁ := b8e378
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e378
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e378
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e378
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e378 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e378
          have b8e2022 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = y := by grind
          clear b8e2020
          have b8e2027 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
            first
            | (have r₁ := b8e2022
               have r₂ := b8e21
               grind)
            | exact resolve b8e2022 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2022
          have b8e2036 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e14 (M.op y y)
               have i₂ := b8e2027
               grind)
            | exact superpose b8e2027 b8e14
            | exact resolve b8e14 b8e2027
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2027
          have b8e2069 : x = (M.op y y) ∨ x = (M.op y y) := by
            first
            | (have i₁ := b8e2036
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e2036
            | exact resolve b8e2036 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2036
          have b8e2070 : x = (M.op y y) := by grind
          clear b8e2069
          have b8e2136 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b8e76 y
               have i₂ := b8e2070
               grind)
            | exact superpose b8e2070 b8e76
            | exact resolve b8e76 b8e2070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e76
          have b8e2142 : (M.op x y) = (M.op y x) := by
            first
            | (have i₁ := b8e13 y y
               have i₂ := b8e2070
               grind)
            | exact superpose b8e2070 b8e13
            | exact resolve b8e13 b8e2070
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2070
          have b8e2162 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e2136
               have i₂ := b8e221
               grind)
            | exact superpose b8e221 b8e2136
            | exact resolve b8e2136 b8e221
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e221 b8e2136
          have b8e2723 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e2162
               grind)
            | exact superpose b8e2162 b8e20
            | exact resolve b8e20 b8e2162
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2162
          have b8e3108 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e2723
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e2723
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e2723
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e2723
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e2723 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2723
          have b8e3117 : (σ (M.op x y)) ≠ (σ (M.op y x)) ∨ x = y := by
            first
            | (have r₁ := b8e3108
               have r₂ := b8e22
               grind)
            | exact resolve b8e3108 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3108
          have b8e3124 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
            first
            | (have r₁ := b8e3117
               have r₂ := b8e21
               grind)
            | exact resolve b8e3117 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3117
          have b8e3125 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e3124
               have i₂ := b8e2142
               grind)
            | exact superpose b8e2142 b8e3124
            | exact resolve b8e3124 b8e2142
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2142 b8e3124
          have b8e3126 : False := by grind
          exact b8e3126

/-- `Equation4388`: `x ◇ (x ◇ x) = (y ◇ y) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4388 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4388 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4388.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e29 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e30 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e29 X0
           have i₂ := b0e30 X0
           grind)
        | exact superpose b0e30 b0e29
        | exact resolve b0e29 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e29
      have b0e35 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e31 (σ y)
           grind)
        | exact superpose b0e31 b0e18
        | exact resolve b0e18 b0e31
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e53 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e55 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e62 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y X1) ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e53 X0 X1 X2
           have i₂ := b0e30 X1
           grind)
        | exact superpose b0e30 b0e53
        | (have j0 := b0e53 X0 X1 X2
           grind)
        | exact resolve b0e53 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e53
      have b0e69 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op y X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e10 X0 X1
           have i₂ := b0e30 X0
           grind)
        | exact superpose b0e30 b0e10
        | exact resolve b0e10 b0e30
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e30
      have b0e87 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 X0 X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e105 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e279 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e61 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e61 b0e15
        | (have j1 := b0e61 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e329 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e62 (σ x) (σ y) X0
           grind)
        | exact superpose b0e62 b0e16
        | (have j1 := b0e62 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e341 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e329 X0
           have i₂ := b0e35
           grind)
        | exact superpose b0e35 b0e329
        | (have j0 := b0e329 X0
           grind)
        | exact resolve b0e329 b0e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35 b0e329
      have b0e517 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 X1 (σ X0)
           have i₂ := b0e58 X0 X0
           grind)
        | exact superpose b0e58 b0e13
        | (have j0 := b0e13 X1 (σ X0)
           have j1 := b0e58 X0 X1
           grind)
        | (have r₁ := b0e13 X0 (σ X0)
           have r₂ := b0e58 X0 X1
           grind)
        | exact resolve b0e13 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e539 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e58 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e548 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e517 X0 X1
           have j1 := b0e13 X1 (σ X0)
           grind)
        | (have r₁ := b0e517 X0 X1
           have r₂ := b0e13 X0 (σ X0)
           grind)
        | exact resolve b0e517 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e517
      have b0e1133 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e87 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e87
        | (have j0 := b0e87 X1 X1
           grind)
        | exact resolve b0e87 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e87
      have b0e1214 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e1133 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e1133
        | (have j0 := b0e1133 X0 X1
           grind)
        | exact resolve b0e1133 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1133
      have b0e1945 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e539 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e539
        | (have j0 := b0e539 (τ X0)
           grind)
        | exact resolve b0e539 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e539
      have b0e1962 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1945 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1945
        | (have j0 := b0e1945 X0
           grind)
        | exact resolve b0e1945 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1945
      have b0e1972 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1962 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1962
        | (have j0 := b0e1962 X0
           grind)
        | exact resolve b0e1962 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1962
      have b0e2354 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e279 x y X0
           grind)
        | exact superpose b0e279 b0e16
        | (have j1 := b0e279 x x X0
           grind)
        | exact resolve b0e16 b0e279
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e279
      have b0e19077 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e2354 X0
           have i₂ := b0e1214 y x
           grind)
        | exact superpose b0e1214 b0e2354
        | (have j0 := b0e2354 X0
           have j1 := b0e1214 X0 x
           grind)
        | (have r₁ := b0e2354 X0
           have r₂ := b0e1214 y x
           grind)
        | exact resolve b0e2354 b0e1214
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1214 b0e2354
      have b0e19079 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e19077 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19077
      have b0e19172 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e105 X0 (σ x)
           have i₂ := b0e19079 (σ X0)
           grind)
        | exact superpose b0e19079 b0e105
        | exact resolve b0e105 b0e19079
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105 b0e19079
      have b0e19200 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e19172 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e19172
        | exact resolve b0e19172 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19172
      have b0e19214 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e19200 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e19200
        | exact resolve b0e19200 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19200
      have b0e19221 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e19214 X0
           have j1 := b0e13 X0 x
           grind)
        | (have r₁ := b0e19214 X0
           have r₂ := b0e13 X0 x
           grind)
        | exact resolve b0e19214 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19214
      have b0e19566 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e548 x X0
           have i₂ := b0e19221 x
           grind)
        | exact superpose b0e19221 b0e548
        | (have j0 := b0e548 x X0
           grind)
        | exact resolve b0e548 b0e19221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e548
      have b0e19568 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e1972 x
           have i₂ := b0e19221 x
           grind)
        | exact superpose b0e19221 b0e1972
        | (have j0 := b0e1972 x
           grind)
        | (have r₁ := b0e1972 x
           have r₂ := b0e19221 x
           grind)
        | exact resolve b0e1972 b0e19221
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1972 b0e19221
      have b0e19612 : x = (M.op x x) := by grind
      clear b0e19568
      have b0e19614 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have j0 := b0e19566 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19566
      have b0e19912 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e69 X0 x
           have i₂ := b0e19612
           grind)
        | exact superpose b0e19612 b0e69
        | exact resolve b0e69 b0e19612
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e69 b0e19612
      have b0e21760 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e341 X0
           have i₂ := b0e19912 y
           grind)
        | exact superpose b0e19912 b0e341
        | (have j0 := b0e341 X0
           grind)
        | exact resolve b0e341 b0e19912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e341
      have b0e21836 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e21760 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e21760
        | (have j0 := b0e21760 X0
           grind)
        | exact resolve b0e21760 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21760
      have b0e21837 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e21836 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21836
      have b0e21841 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e21837 X0
           have i₂ := b0e19614 X0
           grind)
        | exact superpose b0e19614 b0e21837
        | exact resolve b0e21837 b0e19614
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19614 b0e21837
      have b0e22210 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e21841 (σ y)
           grind)
        | exact superpose b0e21841 b0e16
        | exact resolve b0e16 b0e21841
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21841
      have b0e22292 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e22210
           have i₂ := b0e19912 y
           grind)
        | exact superpose b0e19912 b0e22210
        | exact resolve b0e22210 b0e19912
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19912 b0e22210
      have b0e22307 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e22292
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e22292
        | exact resolve b0e22292 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22292
      have b0e22308 : False := by grind
      exact b0e22308
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e45 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e49 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e45 X0
           grind)
        | (have r₁ := b1e45 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e45 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e45 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e45
      have b1e54 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e49 (σ y)
           grind)
        | exact superpose b1e49 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e49 (σ y)
           grind)
        | exact resolve b1e18 b1e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e49
      have b1e60 : False := by grind
      exact b1e60
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e44 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e48 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e44 X0
           grind)
        | (have r₁ := b2e44 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e44 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e44 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e44
      have b2e51 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e48 y
           grind)
        | exact superpose b2e48 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e48 y
           grind)
        | exact resolve b2e17 b2e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e48
      have b2e55 : False := by grind
      exact b2e55
    · have b3e10 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X1) X0) := by
        intro X0 X1
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e19 X0 X1
           grind)
        | exact superpose b3e19 b3e11
        | exact resolve b3e11 b3e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e29 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e31 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e32 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e34 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e31 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31
      have b3e35 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e29 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e29
      have b3e37 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e34 (σ X0)
           grind)
        | exact superpose b3e34 b3e15
        | exact resolve b3e15 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e48 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e25 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e25
        | exact resolve b3e25 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e25
      have b3e90 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e37 y
           grind)
        | exact superpose b3e37 b3e18
        | exact resolve b3e18 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e112 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e35 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e35 b3e15
        | (have j1 := b3e35 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e119 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e90
           have i₂ := b3e35 y y X0
           grind)
        | exact superpose b3e35 b3e90
        | (have j1 := b3e35 y x X0
           grind)
        | exact resolve b3e90 b3e35
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35 b3e90
      have b3e121 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e119 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e119
      have b3e152 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e121 (τ X0)
           grind)
        | exact superpose b3e121 b3e19
        | exact resolve b3e19 b3e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e154 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e152 X0
           have i₂ := b3e34 X0
           grind)
        | exact superpose b3e34 b3e152
        | exact resolve b3e152 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34 b3e152
      have b3e208 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e32 X0 X0
           grind)
        | exact superpose b3e32 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e32 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e32 X0 X1
           grind)
        | exact resolve b3e13 b3e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e227 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e32 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e32
      have b3e230 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e208 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e208 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e208 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e208
      have b3e390 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e154 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e154
        | exact resolve b3e154 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e154
      have b3e418 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e230 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e230
        | (have j0 := b3e230 (τ X0) X1
           grind)
        | exact resolve b3e230 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e230
      have b3e421 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e418 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e418
        | (have j0 := b3e418 X0 X1
           grind)
        | exact resolve b3e418 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e418
      have b3e425 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e421 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e421
        | (have j0 := b3e421 X0 X1
           grind)
        | exact resolve b3e421 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e421
      have b3e439 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e425 (τ X0) X1
           have i₂ := b3e48 X0 X0
           grind)
        | exact superpose b3e48 b3e425
        | (have j0 := b3e425 (τ X0) X1
           grind)
        | exact resolve b3e425 b3e48
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e48 b3e425
      have b3e553 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e10 (σ y) X0
           have i₂ := b3e390 y
           grind)
        | exact superpose b3e390 b3e10
        | exact resolve b3e10 b3e390
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e390
      have b3e564 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (k (M.op y y) y)) := by
        intro X0
        first
        | (have i₁ := b3e553 X0
           have i₂ := b3e37 (M.op y y)
           grind)
        | exact superpose b3e37 b3e553
        | exact resolve b3e553 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37 b3e553
      have b3e570 : ∀ X0 : G, (M.op (M.op X0 X0) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0
        first
        | (have i₁ := b3e564 X0
           have i₂ := b3e121 (M.op y y)
           grind)
        | exact superpose b3e121 b3e564
        | exact resolve b3e564 b3e121
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e121 b3e564
      have b3e572 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e33 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e33
        | (have j0 := b3e33 X1 X1
           grind)
        | exact resolve b3e33 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e633 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e572 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e572
        | (have j0 := b3e572 X0 X1
           grind)
        | exact resolve b3e572 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e572
      have b3e1888 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e227 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e227
        | (have j0 := b3e227 (τ X0)
           grind)
        | exact resolve b3e227 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e1892 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1888 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1888
        | (have j0 := b3e1888 X0
           grind)
        | exact resolve b3e1888 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1888
      have b3e1897 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e1892 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1892
        | (have j0 := b3e1892 X0
           grind)
        | exact resolve b3e1892 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1892
      have b3e2650 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e112 x y X0
           grind)
        | exact superpose b3e112 b3e16
        | (have j1 := b3e112 x x X0
           grind)
        | exact resolve b3e16 b3e112
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e112
      have b3e30684 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e2650 X0
           have i₂ := b3e633 y x
           grind)
        | exact superpose b3e633 b3e2650
        | (have j0 := b3e2650 X0
           have j1 := b3e633 X0 x
           grind)
        | (have r₁ := b3e2650 X0
           have r₂ := b3e633 y x
           grind)
        | exact resolve b3e2650 b3e633
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e633 b3e2650
      have b3e30686 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e30684 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30684
      have b3e30755 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e439 (σ x) X0
           have i₂ := b3e30686 (σ x)
           grind)
        | exact superpose b3e30686 b3e439
        | (have j0 := b3e439 (σ x) X0
           grind)
        | exact resolve b3e439 b3e30686
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e439 b3e30686
      have b3e30815 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e30755 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30755
      have b3e30842 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e30815 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e30815
        | exact resolve b3e30815 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30815
      have b3e30854 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e30842 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e30842 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e30842 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30842
      have b3e31361 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e227 x
           have i₂ := b3e30854 x
           grind)
        | exact superpose b3e30854 b3e227
        | (have j0 := b3e227 x
           grind)
        | exact resolve b3e227 b3e30854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e227
      have b3e31365 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e1897 x
           have i₂ := b3e30854 x
           grind)
        | exact superpose b3e30854 b3e1897
        | (have j0 := b3e1897 x
           grind)
        | (have r₁ := b3e1897 x
           have r₂ := b3e30854 x
           grind)
        | exact resolve b3e1897 b3e30854
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1897 b3e30854
      have b3e31421 : x = (M.op x x) := by grind
      clear b3e31365
      have b3e31425 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e31361
      have b3e31801 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e10 X0 x
           have i₂ := b3e31421
           grind)
        | exact superpose b3e31421 b3e10
        | exact resolve b3e10 b3e31421
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31421
      have b3e36710 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) := by
        first
        | (have i₁ := b3e570 (σ x)
           have i₂ := b3e31425
           grind)
        | exact superpose b3e31425 b3e570
        | exact resolve b3e570 b3e31425
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e570 b3e31425
      have b3e36765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e36710
           have i₂ := b3e31801 y
           grind)
        | exact superpose b3e31801 b3e36710
        | exact resolve b3e36710 b3e31801
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e31801 b3e36710
      have b3e36802 : False := by grind
      exact b3e36802

/-- `Equation4391`: `x ◇ (x ◇ x) = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.  The obligation names no
target, so `gcell`-style reuse can spend it on any law the companion satisfies. -/
theorem GuardAut_pyy_y_x_pyx_Equation4391 :
    AutBox.GuardAut ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4391 := by
  classical
  refine AutBox.guardAut_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hthen helse hcom x y ↦ ?_)
  have hm := (@Law4391.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hthen a b)
  have he : ∀ a b : G, M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id (helse a b)
  have hd := hcom
  clear hthen helse hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b0e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e17 : y = (M.op y y) := by grind
      have b0e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b0e23 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 (τ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e24 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 (τ X0)
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e15
        | exact resolve b0e15 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e31 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 (σ y) (σ y)
           have i₂ := b0e18
           grind)
        | exact superpose b0e18 b0e10
        | exact resolve b0e10 b0e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e32 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e10 X0 y y
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e10
        | exact resolve b0e10 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op (σ y) X0) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b0e31 X0
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e31
        | exact resolve b0e31 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e31
      have b0e37 : (σ y) = (M.op y (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e33 (σ y)
           grind)
        | exact superpose b0e33 b0e18
        | exact resolve b0e18 b0e33
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e54 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e13 X1 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e13
        | (have j0 := b0e13 X1 X0
           have j1 := b0e14 X2 X0
           grind)
        | (have r₁ := b0e13 X0 X1
           have r₂ := b0e14 X0 X1
           grind)
        | exact resolve b0e13 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e55 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X1)) ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X1 X0 X0
           have i₂ := b0e14 X2 X0
           grind)
        | exact superpose b0e14 b0e10
        | (have j1 := b0e14 X2 X0
           grind)
        | exact resolve b0e10 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e14 (σ X1) (σ X0)
           grind)
        | exact superpose b0e14 b0e15
        | (have j1 := b0e14 X0 (σ X0)
           grind)
        | exact resolve b0e15 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b0e54 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e54
      have b0e62 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op y X1) ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e55 X0 X1 X2
           have i₂ := b0e32 X1
           grind)
        | exact superpose b0e32 b0e55
        | (have j0 := b0e55 X0 X1 X2
           grind)
        | exact resolve b0e55 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e55
      have b0e71 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op y X0) := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e10 X0 X1 X2
           have i₂ := b0e32 X0
           grind)
        | exact superpose b0e32 b0e10
        | exact resolve b0e10 b0e32
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e96 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e23 X1 X0
           have i₂ := b0e14 (τ X1) X0
           grind)
        | exact superpose b0e14 b0e23
        | (have j1 := b0e14 X0 X0
           grind)
        | exact resolve b0e23 b0e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e23
      have b0e114 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 (k X0 (τ X1))
           have i₂ := b0e24 X1 X0
           grind)
        | exact superpose b0e24 b0e11
        | exact resolve b0e11 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e283 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b0e15 X1 X0
           have i₂ := b0e61 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b0e61 b0e15
        | (have j1 := b0e61 (σ X0) X2 X2
           grind)
        | exact resolve b0e15 b0e61
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e61
      have b0e333 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op y (σ y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e62 (σ x) (σ y) X0
           grind)
        | exact superpose b0e62 b0e16
        | (have j1 := b0e62 (σ x) x X0
           grind)
        | exact resolve b0e16 b0e62
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e62
      have b0e350 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e333 X0
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e333
        | (have j0 := b0e333 X0
           grind)
        | exact resolve b0e333 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e333
      have b0e523 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b0e13 X1 (σ X0)
           have i₂ := b0e58 X0 X0
           grind)
        | exact superpose b0e58 b0e13
        | (have j0 := b0e13 X1 (σ X0)
           have j1 := b0e58 X0 X1
           grind)
        | (have r₁ := b0e13 X0 (σ X0)
           have r₂ := b0e58 X0 X1
           grind)
        | exact resolve b0e13 b0e58
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e543 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b0e58 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e58
      have b0e553 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b0e523 X0 X1
           have j1 := b0e13 X1 (σ X0)
           grind)
        | (have r₁ := b0e523 X0 X1
           have r₂ := b0e13 X0 (σ X0)
           grind)
        | exact resolve b0e523 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e523
      have b0e982 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e96 X1 (σ X0)
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e96
        | (have j0 := b0e96 X1 X1
           grind)
        | exact resolve b0e96 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e96
      have b0e1057 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e982 X0 X1
           have i₂ := b0e15 X0 X1
           grind)
        | exact superpose b0e15 b0e982
        | (have j0 := b0e982 X0 X1
           grind)
        | exact resolve b0e982 b0e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e982
      have b0e1707 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e543 (τ X0)
           have i₂ := b0e24 X0 (τ X0)
           grind)
        | exact superpose b0e24 b0e543
        | (have j0 := b0e543 (τ X0)
           grind)
        | exact resolve b0e543 b0e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e24 b0e543
      have b0e1723 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b0e1707 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1707
        | (have j0 := b0e1707 X0
           grind)
        | exact resolve b0e1707 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1707
      have b0e1733 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e1723 X0
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e1723
        | (have j0 := b0e1723 X0
           grind)
        | exact resolve b0e1723 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1723
      have b0e2110 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e16
           have i₂ := b0e283 x y X0
           grind)
        | exact superpose b0e283 b0e16
        | (have j1 := b0e283 x x X0
           grind)
        | exact resolve b0e16 b0e283
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e283
      have b0e18273 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e2110 X0
           have i₂ := b0e1057 y x
           grind)
        | exact superpose b0e1057 b0e2110
        | (have j0 := b0e2110 X0
           have j1 := b0e1057 X0 x
           grind)
        | (have r₁ := b0e2110 X0
           have r₂ := b0e1057 y x
           grind)
        | exact resolve b0e2110 b0e1057
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1057 b0e2110
      have b0e18275 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b0e18273 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18273
      have b0e18361 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (σ x))) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e114 X0 (σ x)
           have i₂ := b0e18275 (σ X0)
           grind)
        | exact superpose b0e18275 b0e114
        | exact resolve b0e114 b0e18275
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e114 b0e18275
      have b0e18389 : ∀ X0 : G, (τ (σ X0)) = (k X0 x) ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e18361 X0
           have i₂ := b0e11 x
           grind)
        | exact superpose b0e11 b0e18361
        | exact resolve b0e18361 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18361
      have b0e18403 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b0e18389 X0
           have i₂ := b0e11 X0
           grind)
        | exact superpose b0e11 b0e18389
        | exact resolve b0e18389 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18389
      have b0e18410 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b0e18403 X0
           have j1 := b0e13 X0 x
           grind)
        | (have r₁ := b0e18403 X0
           have r₂ := b0e13 X0 x
           grind)
        | exact resolve b0e18403 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18403
      have b0e18748 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e553 x X0
           have i₂ := b0e18410 x
           grind)
        | exact superpose b0e18410 b0e553
        | (have j0 := b0e553 x X0
           grind)
        | exact resolve b0e553 b0e18410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e553
      have b0e18750 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b0e1733 x
           have i₂ := b0e18410 x
           grind)
        | exact superpose b0e18410 b0e1733
        | (have j0 := b0e1733 x
           grind)
        | (have r₁ := b0e1733 x
           have r₂ := b0e18410 x
           grind)
        | exact resolve b0e1733 b0e18410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e1733 b0e18410
      have b0e18792 : x = (M.op x x) := by grind
      clear b0e18750
      have b0e18794 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have j0 := b0e18748 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18748
      have b0e19094 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b0e71 X0 x x
           have i₂ := b0e18792
           grind)
        | exact superpose b0e18792 b0e71
        | exact resolve b0e71 b0e18792
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18792
      have b0e20861 : ∀ X0 : G, (σ y) ≠ (σ (M.op y y)) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e350 X0
           have i₂ := b0e19094 y
           grind)
        | exact superpose b0e19094 b0e350
        | (have j0 := b0e350 X0
           grind)
        | exact resolve b0e350 b0e19094
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e350 b0e19094
      have b0e20919 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have i₁ := b0e20861 X0
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e20861
        | (have j0 := b0e20861 X0
           grind)
        | exact resolve b0e20861 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20861
      have b0e20920 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
        intro X0
        first
        | (have j0 := b0e20919 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e20919
      have b0e20923 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
        intro X0
        first
        | (have i₁ := b0e20920 X0
           have i₂ := b0e18794 X0
           grind)
        | exact superpose b0e18794 b0e20920
        | exact resolve b0e20920 b0e18794
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e18794 b0e20920
      have b0e21353 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e16
           have i₂ := b0e20923 (σ y)
           grind)
        | exact superpose b0e20923 b0e16
        | exact resolve b0e16 b0e20923
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e21367 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e71 X1 (σ x) X0
           have i₂ := b0e20923 X0
           grind)
        | exact superpose b0e20923 b0e71
        | exact resolve b0e71 b0e20923
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e71 b0e20923
      have b0e21422 : (σ y) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e21353
           have i₂ := b0e21367 x y
           grind)
        | exact superpose b0e21367 b0e21353
        | exact resolve b0e21353 b0e21367
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21353 b0e21367
      have b0e21432 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b0e21422
           have i₂ := b0e17
           grind)
        | exact superpose b0e17 b0e21422
        | exact resolve b0e21422 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e21422
      have b0e21433 : False := by grind
      exact b0e21433
    · have b1e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b1e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b1e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b1e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b1e17 : y = (M.op y y) := by grind
      have b1e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b1e19 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b1e13 X0 y
           have i₂ := b1e17
           grind)
        | exact superpose b1e17 b1e13
        | (have j0 := b1e13 X0 y
           grind)
        | (have r₁ := b1e13 X0 y
           have r₂ := b1e17
           grind)
        | exact resolve b1e13 b1e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e20 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have j0 := b1e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e19
      have b1e21 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b1e15 (τ X0) X1
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e15
        | exact resolve b1e15 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b1e24 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e21 X0 y
           have i₂ := b1e20 (τ X0)
           grind)
        | exact superpose b1e20 b1e21
        | exact resolve b1e21 b1e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e20 b1e21
      have b1e28 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b1e24 X0
           have i₂ := b1e12 X0
           grind)
        | exact superpose b1e12 b1e24
        | exact resolve b1e24 b1e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e24
      have b1e47 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b1e28 X0
           have i₂ := b1e14 X0 (σ y)
           grind)
        | exact superpose b1e14 b1e28
        | (have j1 := b1e14 X0 (σ y)
           grind)
        | exact resolve b1e28 b1e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e28
      have b1e51 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
        intro X0
        first
        | (have j0 := b1e47 X0
           grind)
        | (have r₁ := b1e47 (σ y)
           have r₂ := b1e18
           grind)
        | (have r₁ := b1e47 X0
           have r₂ := b1e18
           grind)
        | exact resolve b1e47 b1e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e47
      have b1e56 : (σ y) ≠ (σ y) := by
        first
        | (have i₁ := b1e18
           have i₂ := b1e51 (σ y)
           grind)
        | exact superpose b1e51 b1e18
        | (have r₁ := b1e18
           have r₂ := b1e51 (σ y)
           grind)
        | exact resolve b1e18 b1e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b1e51
      have b1e62 : False := by grind
      exact b1e62
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b2e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b2e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b2e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b2e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b2e17 : y ≠ (M.op y y) := by grind
      have b2e18 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b2e19 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b2e13 X0 (σ y)
           have i₂ := b2e18
           grind)
        | exact superpose b2e18 b2e13
        | (have j0 := b2e13 X0 (σ y)
           grind)
        | (have r₁ := b2e13 X0 (σ y)
           have r₂ := b2e18
           grind)
        | exact resolve b2e13 b2e18
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b2e20 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
        intro X0
        first
        | (have j0 := b2e19 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e19
      have b2e24 : ∀ X0 : G, (σ X0) = (σ (k X0 y)) := by
        intro X0
        first
        | (have i₁ := b2e15 X0 y
           have i₂ := b2e20 (σ X0)
           grind)
        | exact superpose b2e20 b2e15
        | exact resolve b2e15 b2e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e20
      have b2e27 : ∀ X0 : G, (τ (σ X0)) = (k X0 y) := by
        intro X0
        first
        | (have i₁ := b2e11 (k X0 y)
           have i₂ := b2e24 X0
           grind)
        | exact superpose b2e24 b2e11
        | exact resolve b2e11 b2e24
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e24
      have b2e28 : ∀ X0 : G, (k X0 y) = X0 := by
        intro X0
        first
        | (have i₁ := b2e27 X0
           have i₂ := b2e11 X0
           grind)
        | exact superpose b2e11 b2e27
        | exact resolve b2e27 b2e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e27
      have b2e46 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b2e28 X0
           have i₂ := b2e14 X0 y
           grind)
        | exact superpose b2e14 b2e28
        | (have j1 := b2e14 X0 y
           grind)
        | exact resolve b2e28 b2e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e28
      have b2e50 : ∀ X0 : G, (M.op y X0) = X0 := by
        intro X0
        first
        | (have j0 := b2e46 X0
           grind)
        | (have r₁ := b2e46 y
           have r₂ := b2e17
           grind)
        | (have r₁ := b2e46 X0
           have r₂ := b2e17
           grind)
        | exact resolve b2e46 b2e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e46
      have b2e53 : y ≠ y := by
        first
        | (have i₁ := b2e17
           have i₂ := b2e50 y
           grind)
        | exact superpose b2e50 b2e17
        | (have r₁ := b2e17
           have r₂ := b2e50 y
           grind)
        | exact resolve b2e17 b2e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b2e50
      have b2e57 : False := by grind
      exact b2e57
    · have b3e10 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X0) := by
        intro X0 X1 X2
        grind
      have b3e11 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b3e12 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b3e13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b3e14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
        intro X0 X1
        grind
      have b3e15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b3e16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b3e18 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
      clear hm ht he hd nh hM hi1 hi2 h0a h1a
      have b3e19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 (τ X0) X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e15
        | exact resolve b3e15 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e27 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
        intro X0 X1
        first
        | (have i₁ := b3e11 (k (τ X0) X1)
           have i₂ := b3e19 X0 X1
           grind)
        | exact superpose b3e19 b3e11
        | exact resolve b3e11 b3e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e30 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e13 X1 X0
           have i₂ := b3e14 X2 X0
           grind)
        | exact superpose b3e14 b3e13
        | (have j0 := b3e13 X1 X0
           have j1 := b3e14 X2 X0
           grind)
        | (have r₁ := b3e13 X0 X1
           have r₂ := b3e14 X0 X1
           grind)
        | exact resolve b3e13 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e33 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have i₁ := b3e18
           have i₂ := b3e14 X0 (σ y)
           grind)
        | exact superpose b3e14 b3e18
        | (have j1 := b3e14 X0 (σ y)
           grind)
        | (have r₁ := b3e18
           have r₂ := b3e14 X0 (σ y)
           grind)
        | exact resolve b3e18 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e34 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e14 (σ X1) (σ X0)
           grind)
        | exact superpose b3e14 b3e15
        | (have j1 := b3e14 X0 (σ X0)
           grind)
        | exact resolve b3e15 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e35 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b3e19 X1 X0
           have i₂ := b3e14 (τ X1) X0
           grind)
        | exact superpose b3e14 b3e19
        | (have j1 := b3e14 X0 X0
           grind)
        | exact resolve b3e19 b3e14
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e36 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) := by
        intro X0
        first
        | (have j0 := b3e33 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e33
      have b3e37 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X0 X2) := by
        intro X0 X1 X2
        first
        | (have j0 := b3e30 X0 X1 X2
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e30
      have b3e39 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
        intro X0
        first
        | (have i₁ := b3e15 X0 y
           have i₂ := b3e36 (σ X0)
           grind)
        | exact superpose b3e36 b3e15
        | exact resolve b3e15 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e50 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e27 X1 (τ X0)
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e27
        | exact resolve b3e27 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27
      have b3e96 : (σ y) ≠ (σ (k y y)) := by
        first
        | (have i₁ := b3e18
           have i₂ := b3e39 y
           grind)
        | exact superpose b3e39 b3e18
        | exact resolve b3e18 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e118 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (k X2 (σ X0)) = X2 := by
        intro X0 X1 X2
        first
        | (have i₁ := b3e15 X1 X0
           have i₂ := b3e37 (σ X0) X2 (σ X1)
           grind)
        | exact superpose b3e37 b3e15
        | (have j1 := b3e37 (σ X0) X2 X2
           grind)
        | exact resolve b3e15 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e125 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have i₁ := b3e96
           have i₂ := b3e37 y y X0
           grind)
        | exact superpose b3e37 b3e96
        | (have j1 := b3e37 y x X0
           grind)
        | exact resolve b3e96 b3e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e37 b3e96
      have b3e127 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
        intro X0
        first
        | (have j0 := b3e125 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e125
      have b3e170 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e19 X0 y
           have i₂ := b3e127 (τ X0)
           grind)
        | exact superpose b3e127 b3e19
        | exact resolve b3e19 b3e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e19
      have b3e172 : ∀ X0 : G, (M.op (σ y) X0) = (σ (M.op y (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e170 X0
           have i₂ := b3e36 X0
           grind)
        | exact superpose b3e36 b3e170
        | exact resolve b3e170 b3e36
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e36 b3e170
      have b3e230 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0 X1
        first
        | (have i₁ := b3e13 X1 (σ X0)
           have i₂ := b3e34 X0 X0
           grind)
        | exact superpose b3e34 b3e13
        | (have j0 := b3e13 X1 (σ X0)
           have j1 := b3e34 X0 X1
           grind)
        | (have r₁ := b3e13 X0 (σ X0)
           have r₂ := b3e34 X0 X1
           grind)
        | exact resolve b3e13 b3e34
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b3e247 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
        intro X0
        first
        | (have j0 := b3e34 X0 x
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e34
      have b3e250 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
        intro X0 X1
        first
        | (have j0 := b3e230 X0 X1
           have j1 := b3e13 X1 (σ X0)
           grind)
        | (have r₁ := b3e230 X0 X1
           have r₂ := b3e13 X0 (σ X0)
           grind)
        | exact resolve b3e230 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e230
      have b3e410 : ∀ X0 : G, (M.op (σ y) (σ X0)) = (σ (M.op y X0)) := by
        intro X0
        first
        | (have i₁ := b3e172 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e172
        | exact resolve b3e172 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e172
      have b3e438 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e250 (τ X0) X1
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e250
        | (have j0 := b3e250 (τ X0) X1
           grind)
        | exact resolve b3e250 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e250
      have b3e441 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e438 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e438
        | (have j0 := b3e438 X0 X1
           grind)
        | exact resolve b3e438 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e438
      have b3e445 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e441 X0 X1
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e441
        | (have j0 := b3e441 X0 X1
           grind)
        | exact resolve b3e441 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e441
      have b3e459 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e445 (τ X0) X1
           have i₂ := b3e50 X0 X0
           grind)
        | exact superpose b3e50 b3e445
        | (have j0 := b3e445 (τ X0) X1
           grind)
        | exact resolve b3e445 b3e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e50 b3e445
      have b3e575 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (M.op (σ y) (σ (M.op y y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e10 (σ y) X0 X1
           have i₂ := b3e410 y
           grind)
        | exact superpose b3e410 b3e10
        | exact resolve b3e10 b3e410
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e410
      have b3e583 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (σ (k (M.op y y) y)) := by
        intro X0 X1
        first
        | (have i₁ := b3e575 X0 X1
           have i₂ := b3e39 (M.op y y)
           grind)
        | exact superpose b3e39 b3e575
        | exact resolve b3e575 b3e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e39 b3e575
      have b3e589 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ y)) = (σ (M.op y (M.op y y))) := by
        intro X0 X1
        first
        | (have i₁ := b3e583 X0 X1
           have i₂ := b3e127 (M.op y y)
           grind)
        | exact superpose b3e127 b3e583
        | exact resolve b3e583 b3e127
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e127 b3e583
      have b3e592 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e35 X1 (σ X0)
           have i₂ := b3e11 X0
           grind)
        | exact superpose b3e11 b3e35
        | (have j0 := b3e35 X1 X1
           grind)
        | exact resolve b3e35 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e35
      have b3e652 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b3e592 X0 X1
           have i₂ := b3e15 X0 X1
           grind)
        | exact superpose b3e15 b3e592
        | (have j0 := b3e592 X0 X1
           grind)
        | exact resolve b3e592 b3e15
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e592
      have b3e1266 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e247 (τ X0)
           have i₂ := b3e20 X0 (τ X0)
           grind)
        | exact superpose b3e20 b3e247
        | (have j0 := b3e247 (τ X0)
           grind)
        | exact resolve b3e247 b3e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e20
      have b3e1270 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
        intro X0
        first
        | (have i₁ := b3e1266 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1266
        | (have j0 := b3e1266 X0
           grind)
        | exact resolve b3e1266 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1266
      have b3e1275 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
        intro X0
        first
        | (have i₁ := b3e1270 X0
           have i₂ := b3e12 X0
           grind)
        | exact superpose b3e12 b3e1270
        | (have j0 := b3e1270 X0
           grind)
        | exact resolve b3e1270 b3e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1270
      have b3e2121 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k X0 (σ x)) = X0 := by
        intro X0
        first
        | (have i₁ := b3e16
           have i₂ := b3e118 x y X0
           grind)
        | exact superpose b3e118 b3e16
        | (have j1 := b3e118 x x X0
           grind)
        | exact resolve b3e16 b3e118
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e118
      have b3e26794 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e2121 X0
           have i₂ := b3e652 y x
           grind)
        | exact superpose b3e652 b3e2121
        | (have j0 := b3e2121 X0
           have j1 := b3e652 X0 x
           grind)
        | (have r₁ := b3e2121 X0
           have r₂ := b3e652 y x
           grind)
        | exact resolve b3e2121 b3e652
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e652 b3e2121
      have b3e26796 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e26794 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26794
      have b3e26859 : ∀ X0 : G, (τ (σ x)) ≠ (τ (σ x)) ∨ (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e459 (σ x) X0
           have i₂ := b3e26796 (σ x)
           grind)
        | exact superpose b3e26796 b3e459
        | (have j0 := b3e459 (σ x) X0
           grind)
        | exact resolve b3e459 b3e26796
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e459 b3e26796
      have b3e26917 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have j0 := b3e26859 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26859
      have b3e26940 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x x) := by
        intro X0
        first
        | (have i₁ := b3e26917 X0
           have i₂ := b3e11 x
           grind)
        | exact superpose b3e11 b3e26917
        | exact resolve b3e26917 b3e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26917
      have b3e26952 : ∀ X0 : G, (k X0 x) = X0 := by
        intro X0
        first
        | (have j0 := b3e26940 X0
           have j1 := b3e13 X0 x
           grind)
        | (have r₁ := b3e26940 X0
           have r₂ := b3e13 X0 x
           grind)
        | exact resolve b3e26940 b3e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e26940
      have b3e27413 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b3e247 x
           have i₂ := b3e26952 x
           grind)
        | exact superpose b3e26952 b3e247
        | (have j0 := b3e247 x
           grind)
        | exact resolve b3e247 b3e26952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e247
      have b3e27417 : x ≠ x ∨ x = (M.op x x) := by
        first
        | (have i₁ := b3e1275 x
           have i₂ := b3e26952 x
           grind)
        | exact superpose b3e26952 b3e1275
        | (have j0 := b3e1275 x
           grind)
        | (have r₁ := b3e1275 x
           have r₂ := b3e26952 x
           grind)
        | exact resolve b3e1275 b3e26952
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e1275 b3e26952
      have b3e27471 : x = (M.op x x) := by grind
      clear b3e27417
      have b3e27475 : (σ x) = (M.op (σ x) (σ x)) := by grind
      clear b3e27413
      have b3e27820 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x X0) := by
        intro X0
        first
        | (have i₁ := b3e10 X0 x x
           have i₂ := b3e27471
           grind)
        | exact superpose b3e27471 b3e10
        | exact resolve b3e10 b3e27471
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27471
      have b3e32377 : (M.op (σ x) (σ y)) = (σ (M.op y (M.op y y))) := by
        first
        | (have i₁ := b3e589 (σ x) (σ x)
           have i₂ := b3e27475
           grind)
        | exact superpose b3e27475 b3e589
        | exact resolve b3e589 b3e27475
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e589 b3e27475
      have b3e32416 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b3e32377
           have i₂ := b3e27820 y
           grind)
        | exact superpose b3e27820 b3e32377
        | exact resolve b3e32377 b3e27820
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b3e27820 b3e32377
      have b3e32446 : False := by grind
      exact b3e32446

/-- `Equation4392`: `x ◇ (x ◇ x) = (y ◇ z) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation4392 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4392 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4392.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
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
      have b0e67 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e72 : False := by grind
      exact b0e72
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b4e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
          have b4e32 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 (σ y) X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e13
            | exact resolve b4e13 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
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
          have b4e37 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y y) := by
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
          have b4e39 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
            intro X0
            first
            | (have i₁ := b4e37 X0
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e40 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b4e36 X0
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e36
            | exact resolve b4e36 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e41 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b4e32 X0 X1
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e42 : y = (σ y) := by
            first
            | (have i₁ := b4e40 x
               have i₂ := b4e39 x
               grind)
            | exact superpose b4e39 b4e40
            | exact resolve b4e40 b4e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e39 b4e40
          have b4e56 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b4e63 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b4e56 X0 X1
               have i₂ := b4e30 X0
               grind)
            | exact superpose b4e30 b4e56
            | (have j0 := b4e56 X0 X1
               grind)
            | exact resolve b4e56 b4e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e30 b4e56
          have b4e1070 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e63 x y
               grind)
            | exact superpose b4e63 b4e20
            | (have j1 := b4e63 x (M.op x x)
               grind)
            | exact resolve b4e20 b4e63
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e63
          have b4e1108 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e1070
               have r₂ := b4e23
               grind)
            | exact resolve b4e1070 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1070
          have b4e1691 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e1108
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e1108
            | (have j1 := b4e18 (M.op x x) x
               grind)
            | (have r₁ := b4e1108
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e1108
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e1108 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1108
          have b4e1692 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b4e1691
          have b4e1696 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b4e1692
               have r₂ := b4e21
               grind)
            | exact resolve b4e1692 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1692
          have b4e5556 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e1696
               grind)
            | exact superpose b4e1696 b4e14
            | exact resolve b4e14 b4e1696
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1696
          have b4e5604 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e5556
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e5556
            | exact resolve b4e5556 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5556
          have b4e5605 : x = (M.op x x) := by grind
          clear b4e5604
          have b4e5819 : (σ y) = (M.op x x) := by
            first
            | (have i₁ := b4e41 x x
               have i₂ := b4e5605
               grind)
            | exact superpose b4e5605 b4e41
            | exact resolve b4e41 b4e5605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e5824 : x = (σ y) := by
            first
            | (have i₁ := b4e5819
               have i₂ := b4e5605
               grind)
            | exact superpose b4e5605 b4e5819
            | exact resolve b4e5819 b4e5605
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5605 b4e5819
          have b4e5841 : x = y := by
            first
            | (have i₁ := b4e5824
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e5824
            | exact resolve b4e5824 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e5824
          have b4e5858 : False := by grind
          exact b4e5858
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
          have b5e106 : (σ y) ≠ (σ (M.op y y)) := by
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
          have b5e115 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e106
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e106
            | exact resolve b5e106 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e106
          have b5e116 : False := by grind
          exact b5e116
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
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
          have b7e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 (σ y) (σ y)
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
            intro X0
            first
            | (have i₁ := b7e34 X0
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e34
            | exact resolve b7e34 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e34
          have b7e43 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op X1 X1)
               have i₂ := b7e38 X1
               grind)
            | exact superpose b7e38 b7e13
            | exact resolve b7e13 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e44 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b7e43 x X1
               have i₂ := b7e38 x
               grind)
            | exact superpose b7e38 b7e43
            | exact resolve b7e43 b7e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e38 b7e43
          have b7e107 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e44 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e44
            | exact resolve b7e44 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e44
          have b7e119 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e107
               grind)
            | exact superpose b7e107 b7e14
            | exact resolve b7e14 b7e107
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e107
          have b7e120 : y = (M.op y y) := by
            first
            | (have i₁ := b7e119
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e119
            | exact resolve b7e119 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e119
          have b7e124 : False := by grind
          exact b7e124
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X1) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e32 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X3 X4) X3) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e13 x X3 X4
               have i₂ := b8e13 x X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e33 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X0) X3) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X2 X3 (M.op X3 X3)
               have i₂ := b8e13 X3 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e35 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e13 X1 x x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e40 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b8e56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e61 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
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
          have b8e62 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have j0 := b8e61 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e61
          have b8e64 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e56 X0 X1
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e56
            | (have j0 := b8e56 X0 X1
               grind)
            | exact resolve b8e56 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e56
          have b8e70 : (σ y) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b8e24
               have i₂ := b8e30 y
               grind)
            | exact superpose b8e30 b8e24
            | exact resolve b8e24 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e103 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e35 X1 (σ X0)
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e35
            | exact resolve b8e35 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30
          have b8e132 : ∀ X0 X1 X2 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X0) X2) = (M.op (M.op (M.op X4 X5) X4) X6) := by
            intro X0 X1 X2 X4 X5 X6
            first
            | (have i₁ := b8e33 X4 X5 x X6
               have i₂ := b8e33 X0 X1 x X2
               grind)
            | (have i₁ := b8e33 X0 X1 (M.op (M.op X0 X1) X0) x
               have i₂ := b8e33 X0 X1 X2 (M.op (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0))
               grind)
            | exact superpose b8e33 b8e33
            | exact resolve b8e33 b8e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33
          have b8e195 : ∀ X0 : G, (k (τ X0) y) = (τ (M.op (σ y) X0)) ∨ (σ y) = X0 := by
            intro X0
            first
            | (have i₁ := b8e40 X0 y
               have i₂ := b8e62 X0
               grind)
            | exact superpose b8e62 b8e40
            | (have j1 := b8e62 X0
               grind)
            | exact resolve b8e40 b8e62
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e40 b8e62
          have b8e663 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e64 x y
               grind)
            | exact superpose b8e64 b8e20
            | (have j1 := b8e64 x (M.op x x)
               grind)
            | exact resolve b8e20 b8e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e693 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e663
               have r₂ := b8e23
               grind)
            | exact resolve b8e663 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e663
          have b8e1995 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (k (τ (σ (M.op y y))) y) ∨ (σ y) = (σ (M.op y y)) := by
            intro X0
            first
            | (have i₁ := b8e195 (σ (M.op y y))
               have i₂ := b8e103 y X0
               grind)
            | exact superpose b8e103 b8e195
            | (have j0 := b8e195 (σ (M.op y y))
               grind)
            | exact resolve b8e195 b8e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103 b8e195
          have b8e2034 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (k (τ (σ (M.op y y))) y) := by
            intro X0
            first
            | (have j0 := b8e1995 X0
               grind)
            | (have r₁ := b8e1995 X0
               have r₂ := b8e70
               grind)
            | exact resolve b8e1995 b8e70
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e70 b8e1995
          have b8e2047 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (k (M.op y y) y) := by
            intro X0
            first
            | (have i₁ := b8e2034 X0
               have i₂ := b8e14 (M.op y y)
               grind)
            | exact superpose b8e14 b8e2034
            | exact resolve b8e2034 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2034
          have b8e2736 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (k (M.op y y) y)) := by
            intro X0
            first
            | (have i₁ := b8e15 (M.op X0 (M.op X0 X0))
               have i₂ := b8e2047 X0
               grind)
            | exact superpose b8e2047 b8e15
            | exact resolve b8e15 b8e2047
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2047
          have b8e3759 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have i₁ := b8e2736 X0
               have i₂ := b8e18 (M.op y y) y
               grind)
            | exact superpose b8e18 b8e2736
            | (have j1 := b8e18 (M.op y y) y
               grind)
            | exact resolve b8e2736 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2736
          have b8e3835 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by
            intro X0
            first
            | (have j0 := b8e3759 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3759
          have b8e3857 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op y (M.op y y))) := by
            intro X0
            first
            | (have j0 := b8e3835 X0
               grind)
            | (have r₁ := b8e3835 X0
               have r₂ := b8e22
               grind)
            | exact resolve b8e3835 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3835
          have b8e5708 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (M.op X0 (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e3857 X1
               have i₂ := b8e35 y X0
               grind)
            | (have i₁ := b8e3857 X1
               have i₂ := b8e35 X0 y
               grind)
            | exact superpose b8e35 b8e3857
            | exact resolve b8e3857 b8e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e35 b8e3857
          have b8e8538 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e693
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e693
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e693
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e693
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e693 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e693
          have b8e8539 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e8538
          have b8e8541 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e8539
               have r₂ := b8e21
               grind)
            | exact resolve b8e8539 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8539
          have b8e8549 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e8541
               grind)
            | exact superpose b8e8541 b8e14
            | exact resolve b8e14 b8e8541
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8541
          have b8e8587 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e8549
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e8549
            | exact resolve b8e8549 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8549
          have b8e8588 : x = (M.op x x) := by grind
          clear b8e8587
          have b8e8697 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b8e5708 x X0
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e5708
            | exact resolve b8e5708 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5708
          have b8e8698 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e13
            | exact resolve b8e13 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e8700 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x x) := by
            intro X0 X1
            first
            | (have i₁ := b8e32 X0 X1 x x
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e32
            | exact resolve b8e32 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e8730 : ∀ X0 X1 : G, x = (M.op (M.op X0 X1) X0) := by
            intro X0 X1
            first
            | (have i₁ := b8e8700 X0 X1
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e8700
            | exact resolve b8e8700 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8700
          have b8e8732 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e8698 X0
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e8698
            | exact resolve b8e8698 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8698
          have b8e8733 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e8697 X0
               have i₂ := b8e8588
               grind)
            | exact superpose b8e8588 b8e8697
            | exact resolve b8e8697 b8e8588
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8588 b8e8697
          have b8e8755 : x = (σ x) := by
            first
            | (have i₁ := b8e8733 x
               have i₂ := b8e8732 x
               grind)
            | exact superpose b8e8732 b8e8733
            | exact resolve b8e8733 b8e8732
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8732 b8e8733
          have b8e11082 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e8755
               grind)
            | exact superpose b8e8755 b8e20
            | exact resolve b8e20 b8e8755
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e12045 : ∀ X0 X1 X2 : G, x = (M.op (M.op (M.op X0 X1) X0) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e132 X0 X1 X2 x x (M.op x x)
               have i₂ := b8e8730 (M.op x x) x
               grind)
            | exact superpose b8e8730 b8e132
            | exact resolve b8e132 b8e8730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e132
          have b8e12108 : ∀ X2 : G, x = (M.op x X2) := by
            intro X2
            first
            | (have i₁ := b8e12045 x x X2
               have i₂ := b8e8730 x x
               grind)
            | exact superpose b8e8730 b8e12045
            | exact resolve b8e12045 b8e8730
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e8730 b8e12045
          have b8e39974 : x ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e11082
               have i₂ := b8e12108 (σ y)
               grind)
            | exact superpose b8e12108 b8e11082
            | exact resolve b8e11082 b8e12108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e11082
          have b8e39975 : x ≠ (σ x) := by
            first
            | (have i₁ := b8e39974
               have i₂ := b8e12108 y
               grind)
            | exact superpose b8e12108 b8e39974
            | exact resolve b8e39974 b8e12108
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e12108 b8e39974
          have b8e39976 : False := by grind
          exact b8e39976
