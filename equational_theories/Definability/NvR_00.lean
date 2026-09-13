import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1076 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1076 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e49
        | exact resolve b0e49 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e49
      have b0e185 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e54 x
           grind)
        | exact superpose b0e54 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e54 x
           grind)
        | exact resolve b0e22 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e54
      have b0e195 : False := by grind
      exact b0e195
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
        have b1e49 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e51
        have b1e55 : (k x y) = (M.op y y) := by grind
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
        have b1e74 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e124 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
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
        have b1e622 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e74 (σ x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e74
          | (have j0 := b1e74 (σ x)
             grind)
          | (have r₁ := b1e74 (σ x)
             have r₂ := b1e57
             grind)
          | exact resolve b1e74 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e74
        have b1e623 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e622
        have b1e624 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e623
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e623
          | exact resolve b1e623 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e623
        have b1e625 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e624
             have r₂ := b1e124
             grind)
          | exact resolve b1e624 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e624
        have b1e626 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e625
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e625
          | exact resolve b1e625 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e625
        have b1e627 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e626
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e626
          | exact resolve b1e626 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e626
        have b1e628 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e627
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e627
          | exact resolve b1e627 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e627
        have b1e629 : False := by grind
        exact b1e629
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
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e51 : (k x y) = (M.op y y) := by grind
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
        have b2e134 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e60 y
             grind)
          | exact superpose b2e60 b2e22
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e986 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e987 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e986
             have r₂ := b2e21
             grind)
          | exact resolve b2e986 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e986
        have b2e988 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e987
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e987
          | exact resolve b2e987 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e987
        have b2e989 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e988
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e988
          | exact resolve b2e988 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e988
        have b2e990 : False := by grind
        exact b2e990
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
        have b3e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e54 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e51
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
        have b3e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e53 (σ X0)
             grind)
          | exact superpose b3e53 b3e18
          | exact resolve b3e18 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e59
          | exact resolve b3e59 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
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
        have b3e78 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
        have b3e79 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e78
          | exact resolve b3e78 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e79
          | exact resolve b3e79 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e79
        have b3e81 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e80
          | exact resolve b3e80 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e183 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e66 x
             grind)
          | exact superpose b3e66 b3e23
          | exact resolve b3e23 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e66
        have b3e230 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e231 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e230
             have r₂ := b3e20
             grind)
          | exact resolve b3e230 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e230
        have b3e235 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e231
             grind)
          | exact superpose b3e231 b3e81
          | exact resolve b3e81 b3e231
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e231
        have b3e239 : False := by grind
        exact b3e239
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
          have b4e64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b4e64
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
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e68
            | exact resolve b5e68 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e68
          have b5e85 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e120 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e256 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e257 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e256
               have r₂ := b5e21
               grind)
            | exact resolve b5e256 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e256
          have b5e1233 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1234 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1233
               have r₂ := b5e23
               grind)
            | exact resolve b5e1233 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1233
          have b5e1235 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1234
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1234
            | exact resolve b5e1234 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1234
          have b5e1236 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1235
               have i₂ := b5e257
               grind)
            | exact superpose b5e257 b5e1235
            | exact resolve b5e1235 b5e257
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e257 b5e1235
          have b5e1239 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1236
               grind)
            | exact superpose b5e1236 b5e23
            | exact resolve b5e23 b5e1236
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1236
          have b5e1250 : False := by grind
          exact b5e1250
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
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e15
          | exact resolve b6e15 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e72 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e70
        have b6e73 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e72
          | exact resolve b6e72 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e74 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e50 y
             grind)
          | exact superpose b6e50 b6e73
          | exact resolve b6e73 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e73
        have b6e125 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e74
             grind)
          | exact superpose b6e74 b6e13
          | exact resolve b6e13 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e126 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e125
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e125
          | exact resolve b6e125 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e142 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e126
             grind)
          | exact superpose b6e126 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e143 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e142
        have b6e145 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e143
             have r₂ := b6e21
             grind)
          | exact resolve b6e143 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e143
        have b6e147 : False := by grind
        exact b6e147
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
          have b7e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b7e62
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
          have b7e86 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e86 X0
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e86
            | (have j0 := b7e86 X0
               grind)
            | exact resolve b7e86 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e23
            | exact resolve b7e23 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e89
            | exact resolve b7e89 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e608 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e88 (σ x)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e88
            | (have j0 := b7e88 (σ x)
               grind)
            | (have r₁ := b7e88 (σ x)
               have r₂ := b7e67
               grind)
            | exact resolve b7e88 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e88
          have b7e609 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e608
          have b7e610 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e609
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e609
            | exact resolve b7e609 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e609
          have b7e611 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e610
               have r₂ := b7e94
               grind)
            | exact resolve b7e610 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e610
          have b7e612 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e611
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e611
            | exact resolve b7e611 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e611
          have b7e613 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e612
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e612
            | exact resolve b7e612 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e612
          have b7e615 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e613
               have i₂ := b7e128 x y
               grind)
            | exact superpose b7e128 b7e613
            | (have j1 := b7e128 x y
               grind)
            | exact resolve b7e613 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e617 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e613
               grind)
            | exact superpose b7e613 b7e14
            | exact resolve b7e14 b7e613
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e613
          have b7e636 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e617
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e617
            | exact resolve b7e617 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e617
          have b7e638 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e615
               have r₂ := b7e94
               grind)
            | exact resolve b7e615 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e615
          have b7e641 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e638
               have r₂ := b7e22
               grind)
            | exact resolve b7e638 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e638
          have b7e642 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e641
               have i₂ := b7e636
               grind)
            | exact superpose b7e636 b7e641
            | exact resolve b7e641 b7e636
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e636 b7e641
          have b7e643 : False := by grind
          exact b7e643
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
          have b8e113 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1031 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1032 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1031
               have r₂ := b8e23
               grind)
            | exact resolve b8e1031 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1031
          have b8e1033 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1032
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1032
            | exact resolve b8e1032 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1032
          have b8e1038 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1033
               grind)
            | exact superpose b8e1033 b8e20
            | exact resolve b8e20 b8e1033
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1033
          have b8e1106 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1038
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1038
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1038 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1038
          have b8e1107 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1106
          have b8e1109 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1107
               have r₂ := b8e21
               grind)
            | exact resolve b8e1107 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1107
          have b8e1112 : False := by grind
          exact b8e1112

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_y_x_pyx_Equation1076 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
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
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : x = (M.op y x) := by grind
      have b0e20 : (σ x) = (M.op (σ y) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : y = (M.op x (M.op (M.op y x) x)) := by
        first
        | (have i₁ := b0e11 y x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : y = (M.op x (M.op x x)) := by
        first
        | (have i₁ := b0e32
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e38 : x = (M.op x (M.op y x)) := by
        first
        | (have i₁ := b0e11 x x
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e11
        | exact resolve b0e11 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41 : x = (M.op x x) := by
        first
        | (have i₁ := b0e38
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e38
        | exact resolve b0e38 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38
      have b0e45 : y = (M.op x x) := by
        first
        | (have i₁ := b0e37
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e37
        | exact resolve b0e37 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37
      have b0e50 : x = y := by
        first
        | (have i₁ := b0e45
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e45
        | exact resolve b0e45 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e45
      have b0e59 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e50
           grind)
        | exact superpose b0e50 b0e18
        | exact resolve b0e18 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e61 : (σ x) = (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e20
           have i₂ := b0e50
           grind)
        | exact superpose b0e50 b0e20
        | exact resolve b0e20 b0e50
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e63 : (σ x) ≠ (M.op (σ x) (σ x)) := by
        first
        | (have i₁ := b0e59
           have i₂ := b0e41
           grind)
        | exact superpose b0e41 b0e59
        | exact resolve b0e59 b0e41
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41 b0e59
      have b0e64 : False := by grind
      exact b0e64
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
        have b1e39 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e41 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e39
        have b1e43 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e41
             have r₂ := b1e23
             grind)
          | exact resolve b1e41 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e41
        have b1e44 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e43
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e43
          | exact resolve b1e43 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e43
        have b1e45 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e44
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e44
          | exact resolve b1e44 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e44
        have b1e46 : False := by grind
        exact b1e46
      · have b2e12 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
          intro X0 X1
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
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
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e27 : y = (M.op x (M.op (M.op y x) x)) := by
          first
          | (have i₁ := b2e12 y x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e12
          | exact resolve b2e12 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : y = (M.op x (M.op x x)) := by
          first
          | (have i₁ := b2e27
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e27
          | exact resolve b2e27 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e27
        have b2e31 : x = (M.op x (M.op y x)) := by
          first
          | (have i₁ := b2e12 x x
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e12
          | exact resolve b2e12 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e34 : x = (M.op x x) := by
          first
          | (have i₁ := b2e31
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e31
          | exact resolve b2e31 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e31
        have b2e38 : y = (M.op x x) := by
          first
          | (have i₁ := b2e30
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e30
          | exact resolve b2e30 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30
        have b2e40 : x ≠ x ∨ x = (k x x) := by
          first
          | (have i₁ := b2e15 x x
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e15
          | (have j0 := b2e15 x x
             grind)
          | (have r₁ := b2e15 x x
             have r₂ := b2e34
             grind)
          | exact resolve b2e15 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e41 : x = (k x x) := by grind
        clear b2e40
        have b2e43 : x = y := by
          first
          | (have i₁ := b2e38
             have i₂ := b2e34
             grind)
          | exact superpose b2e34 b2e38
          | exact resolve b2e38 b2e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e34 b2e38
        have b2e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e54 : (σ x) ≠ (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e43
             grind)
          | exact superpose b2e43 b2e21
          | exact resolve b2e21 b2e43
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e171 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
          first
          | (have i₁ := b2e54
             have i₂ := b2e48 x x
             grind)
          | exact superpose b2e48 b2e54
          | (have j1 := b2e48 x x
             grind)
          | (have r₁ := b2e54
             have r₂ := b2e48 x x
             grind)
          | exact resolve b2e54 b2e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e48
        have b2e180 : (σ x) ≠ (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
        clear b2e171
        have b2e181 : (σ x) ≠ (σ (k x x)) := by
          first
          | (have r₁ := b2e180
             have r₂ := b2e54
             grind)
          | exact resolve b2e180 b2e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e54 b2e180
        have b2e185 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e181
             have i₂ := b2e41
             grind)
          | exact superpose b2e41 b2e181
          | exact resolve b2e181 b2e41
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e41 b2e181
        have b2e186 : False := by grind
        exact b2e186
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
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
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
          have b4e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b4e53 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = (M.op X0 (τ X1)) := by
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
          have b4e56 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
          have b4e66 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e56 X1 (τ X0)
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e56
            | exact resolve b4e56 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e56
          have b4e141 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e48 x y
               grind)
            | exact superpose b4e48 b4e20
            | (have j1 := b4e48 x y
               grind)
            | exact resolve b4e20 b4e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e148 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e149 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b4e48 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48
          have b4e397 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e53 X0 (σ X0)
               have i₂ := b4e14 X0
               grind)
            | exact superpose b4e14 b4e53
            | exact resolve b4e53 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e53
          have b4e430 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e397 X0 X1
               have i₂ := b4e19 X0 X1
               grind)
            | exact superpose b4e19 b4e397
            | (have j0 := b4e397 X0 X1
               grind)
            | exact resolve b4e397 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e397
          have b4e526 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e148 (τ X1) (τ X0)
               have i₂ := b4e66 X1 X0
               grind)
            | exact superpose b4e66 b4e148
            | (have j0 := b4e148 (τ X1) (τ X0)
               grind)
            | exact resolve b4e148 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e148
          have b4e535 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e526 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e526
            | (have j0 := b4e526 X0 X1
               grind)
            | exact resolve b4e526 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e526
          have b4e538 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e535 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e535
            | (have j0 := b4e535 X0 X1
               grind)
            | exact resolve b4e535 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e535
          have b4e540 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b4e541 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e540 X0 X0
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e540
            | (have j0 := b4e540 X0 X1
               grind)
            | exact resolve b4e540 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e540
          have b4e542 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b4e541 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e541
            | (have j0 := b4e541 X0 X1
               grind)
            | exact resolve b4e541 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e541
          have b4e543 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e542 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e542
            | (have j0 := b4e542 X0 X1
               grind)
            | exact resolve b4e542 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e542
          have b4e557 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e149 (τ X1) (τ X0)
               have i₂ := b4e66 X1 X0
               grind)
            | exact superpose b4e66 b4e149
            | (have j0 := b4e149 (τ X1) (τ X0)
               grind)
            | exact resolve b4e149 b4e66
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e66
          have b4e567 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e557 X0 X1
               have i₂ := b4e15 (k X0 X1)
               grind)
            | exact superpose b4e15 b4e557
            | (have j0 := b4e557 X0 X1
               grind)
            | exact resolve b4e557 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e557
          have b4e570 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e567 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e567
            | (have j0 := b4e567 X0 X1
               grind)
            | exact resolve b4e567 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e567
          have b4e572 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e570 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e570
            | (have j0 := b4e570 X0 X1
               grind)
            | exact resolve b4e570 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e570
          have b4e573 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b4e572 X0 X0
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
          have b4e574 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e573 X0 X1
               have i₂ := b4e15 X0
               grind)
            | exact superpose b4e15 b4e573
            | (have j0 := b4e573 X0 X1
               grind)
            | exact resolve b4e573 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e573
          have b4e575 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b4e574 X0 X1
               have i₂ := b4e15 X1
               grind)
            | exact superpose b4e15 b4e574
            | (have j0 := b4e574 X0 X1
               grind)
            | exact resolve b4e574 b4e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e574
          have b4e600 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e141
               have i₂ := b4e430 y x
               grind)
            | exact superpose b4e430 b4e141
            | (have j1 := b4e430 (σ y) (σ x)
               grind)
            | (have r₁ := b4e141
               have r₂ := b4e430 y x
               grind)
            | exact resolve b4e141 b4e430
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e141 b4e430
          have b4e601 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e600
          have b4e45767 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e601
               grind)
            | exact superpose b4e601 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e601
               grind)
            | (have r₁ := b4e16 y x
               have r₂ := b4e601
               grind)
            | exact resolve b4e16 b4e601
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e601
          have b4e45786 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e45767
          have b4e45802 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e45786
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e45786
            | exact resolve b4e45786 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45786
          have b4e46939 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e17 (σ y) (σ x)
               have i₂ := b4e45802
               grind)
            | exact superpose b4e45802 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 (σ y) (σ x)
               have r₂ := b4e45802
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e45802
               grind)
            | exact resolve b4e17 b4e45802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45802
          have b4e46957 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b4e46939
          have b4e46975 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b4e46957
               have r₂ := b4e25
               grind)
            | exact resolve b4e46957 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46957
          have b4e46987 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e46975
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e46975
            | exact resolve b4e46975 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46975
          have b4e48175 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e46987
               grind)
            | exact superpose b4e46987 b4e14
            | exact resolve b4e14 b4e46987
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e46987
          have b4e48396 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e48175
               have i₂ := b4e14 y
               grind)
            | exact superpose b4e14 b4e48175
            | exact resolve b4e48175 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48175
          have b4e48397 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b4e575 y x
               grind)
            | (have r₁ := b4e48396
               have r₂ := b4e575 y x
               grind)
            | exact resolve b4e48396 b4e575
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e575 b4e48396
          have b4e49061 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e14 (k y x)
               have i₂ := b4e48397
               grind)
            | exact superpose b4e48397 b4e14
            | exact resolve b4e14 b4e48397
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e48397
          have b4e49283 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b4e49061
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e49061
            | exact resolve b4e49061 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49061
          have b4e49284 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b4e543 y x
               grind)
            | (have r₁ := b4e49283
               have r₂ := b4e543 y x
               grind)
            | exact resolve b4e49283 b4e543
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e543 b4e49283
          have b4e49854 : x = (M.op y (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e13 x y
               have i₂ := b4e49284
               grind)
            | exact superpose b4e49284 b4e13
            | exact resolve b4e13 b4e49284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e51929 : x = (M.op y (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e49854
               have i₂ := b4e49284
               grind)
            | exact superpose b4e49284 b4e49854
            | exact resolve b4e49854 b4e49284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49854
          have b4e51962 : x = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e51929
               have r₂ := b4e26
               grind)
            | exact resolve b4e51929 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51929
          have b4e52472 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e13 y y
               have i₂ := b4e51962
               grind)
            | exact superpose b4e51962 b4e13
            | exact resolve b4e13 b4e51962
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e52960 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e52472
               have i₂ := b4e49284
               grind)
            | exact superpose b4e49284 b4e52472
            | exact resolve b4e52472 b4e49284
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e49284 b4e52472
          have b4e52988 : y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b4e52960
               have r₂ := b4e26
               grind)
            | exact resolve b4e52960 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52960
          have b4e53534 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e51962
               have i₂ := b4e52988
               grind)
            | exact superpose b4e52988 b4e51962
            | exact resolve b4e51962 b4e52988
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e51962
          have b4e53556 : x = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b4e53534
          have b4e54765 : x = y ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b4e52988
               have i₂ := b4e53556
               grind)
            | exact superpose b4e53556 b4e52988
            | exact resolve b4e52988 b4e53556
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e52988 b4e53556
          have b4e54787 : x = y ∨ x = (M.op x y) := by grind
          clear b4e54765
          have b4e54810 : x = (M.op x y) := by
            first
            | (have r₁ := b4e54787
               have r₂ := b4e26
               grind)
            | exact resolve b4e54787 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54787
          have b4e55351 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b4e17 y x
               have i₂ := b4e54810
               grind)
            | exact superpose b4e54810 b4e17
            | (have j0 := b4e17 y x
               grind)
            | (have r₁ := b4e17 y x
               have r₂ := b4e54810
               grind)
            | exact resolve b4e17 b4e54810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e55369 : x = y ∨ y = (k y x) := by grind
          clear b4e55351
          have b4e55385 : y = (k y x) := by
            first
            | (have r₁ := b4e55369
               have r₂ := b4e26
               grind)
            | exact resolve b4e55369 b4e26
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e26 b4e55369
          have b4e55881 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e149 x y
               have i₂ := b4e55385
               grind)
            | exact superpose b4e55385 b4e149
            | (have j0 := b4e149 x y
               grind)
            | exact resolve b4e149 b4e55385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e149
          have b4e55921 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e55881
          have b4e67333 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e16 (σ y) (σ x)
               have i₂ := b4e55921
               grind)
            | exact superpose b4e55921 b4e16
            | (have j0 := b4e16 (σ y) (σ x)
               grind)
            | (have r₁ := b4e16 (σ y) (σ x)
               have r₂ := b4e55921
               grind)
            | exact resolve b4e16 b4e55921
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55921
          have b4e67352 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b4e67333
          have b4e67368 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e67352
               have i₂ := b4e19 y x
               grind)
            | exact superpose b4e19 b4e67352
            | exact resolve b4e67352 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67352
          have b4e67375 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e67368
               have i₂ := b4e55385
               grind)
            | exact superpose b4e55385 b4e67368
            | exact resolve b4e67368 b4e55385
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e55385 b4e67368
          have b4e67376 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b4e67375
               have r₂ := b4e25
               grind)
            | exact resolve b4e67375 b4e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e25 b4e67375
          have b4e67851 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e67376
               grind)
            | exact superpose b4e67376 b4e20
            | exact resolve b4e20 b4e67376
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e67376
          have b4e67905 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b4e67851
               have i₂ := b4e54810
               grind)
            | exact superpose b4e54810 b4e67851
            | exact resolve b4e67851 b4e54810
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e54810 b4e67851
          have b4e67906 : False := by grind
          exact b4e67906
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
          have b5e34 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          clear b5e34
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
          have b5e125 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e41 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e41
          have b5e516 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have i₁ := b5e125 y x
               have i₂ := b5e38
               grind)
            | exact superpose b5e38 b5e125
            | (have j0 := b5e125 y x
               grind)
            | exact resolve b5e125 b5e38
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e38 b5e125
          have b5e520 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
          clear b5e516
          have b5e523 : (σ x) = (M.op (σ y) (σ x)) := by
            first
            | (have r₁ := b5e520
               have r₂ := b5e24
               grind)
            | exact resolve b5e520 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e520
          have b5e527 : False := by grind
          exact b5e527
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
        have b6e67 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op y x) := by
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
        have b6e69 : y = (M.op y x) ∨ x = (M.op y x) := by grind
        clear b6e67
        have b6e72 : x = (M.op y x) := by
          first
          | (have r₁ := b6e69
             have r₂ := b6e21
             grind)
          | exact resolve b6e69 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e69
        have b6e75 : False := by grind
        exact b6e75
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
        · have b8e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
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
          have b8e21 : x ≠ (M.op y x) := by grind
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
          have b8e97 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
          have b8e104 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e105 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e324 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e104 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e104
            | (have j0 := b8e104 (τ X1) (τ X0)
               grind)
            | exact resolve b8e104 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e104
          have b8e331 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e324 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e324
            | (have j0 := b8e324 X0 X1
               grind)
            | exact resolve b8e324 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e324
          have b8e334 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e331 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e331
            | (have j0 := b8e331 X0 X1
               grind)
            | exact resolve b8e331 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e331
          have b8e336 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e334 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e334
            | (have j0 := b8e334 X0 X1
               grind)
            | exact resolve b8e334 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e334
          have b8e337 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e336 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e336
            | (have j0 := b8e336 X0 X1
               grind)
            | exact resolve b8e336 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e336
          have b8e338 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e337 X0 X1
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
          have b8e339 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b8e338 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e338
            | (have j0 := b8e338 X0 X1
               grind)
            | exact resolve b8e338 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e338
          have b8e384 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          clear b8e46
          have b8e391 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e394 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e391 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e391
            | (have j0 := b8e391 X0 X1
               grind)
            | exact resolve b8e391 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e391
          have b8e396 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e397 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e398 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) ≠ X0 := by
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
          have b8e399 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
          have b8e444 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e97
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e97
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e97 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e97
          have b8e445 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e444
          have b8e3735 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e445
               grind)
            | exact superpose b8e445 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e445
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e445
               grind)
            | exact resolve b8e16 b8e445
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e445
          have b8e3752 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e3735
          have b8e3753 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e3752
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3752
            | exact resolve b8e3752 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3752
          have b8e21686 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3753
               grind)
            | exact superpose b8e3753 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3753
               grind)
            | exact resolve b8e16 b8e3753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e21687 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e3753
               grind)
            | exact superpose b8e3753 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e3753
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e3753
               grind)
            | exact resolve b8e17 b8e3753
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3753
          have b8e21704 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e21687
          have b8e21713 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e21704
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e21704
            | exact resolve b8e21704 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21704
          have b8e21714 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e21686
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e21686
            | exact resolve b8e21686 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21686
          have b8e21715 : (σ x) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e21714
          have b8e135688 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e21713
               grind)
            | exact superpose b8e21713 b8e14
            | exact resolve b8e14 b8e21713
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21713
          have b8e135729 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e135688
               have r₂ := b8e21715
               grind)
            | exact resolve b8e135688 b8e21715
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e21715 b8e135688
          have b8e135747 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e135729
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e135729
            | exact resolve b8e135729 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135729
          have b8e135748 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have j1 := b8e399 y x
               grind)
            | (have r₁ := b8e135747
               have r₂ := b8e399 y x
               grind)
            | exact resolve b8e135747 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e135747
          have b8e136005 : (k y x) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e135748
               grind)
            | exact superpose b8e135748 b8e14
            | exact resolve b8e14 b8e135748
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e135748
          have b8e136180 : x = (k y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e136005
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e136005
            | exact resolve b8e136005 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136005
          have b8e136181 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e339 y x
               grind)
            | (have r₁ := b8e136180
               have r₂ := b8e339 y x
               grind)
            | exact resolve b8e136180 b8e339
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e339 b8e136180
          have b8e136406 : x = (M.op y (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e13 x y
               have i₂ := b8e136181
               grind)
            | exact superpose b8e136181 b8e13
            | exact resolve b8e13 b8e136181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e136421 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e137340 : x = (M.op y (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e136406
               have i₂ := b8e136181
               grind)
            | exact superpose b8e136181 b8e136406
            | exact resolve b8e136406 b8e136181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136406
          have b8e137348 : x = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e137340
               have r₂ := b8e136421
               grind)
            | exact resolve b8e137340 b8e136421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137340
          have b8e137595 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e13 y y
               have i₂ := b8e137348
               grind)
            | exact superpose b8e137348 b8e13
            | exact resolve b8e13 b8e137348
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e137813 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e137595
               have i₂ := b8e136181
               grind)
            | exact superpose b8e136181 b8e137595
            | exact resolve b8e137595 b8e136181
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136181 b8e137595
          have b8e137830 : y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e137813
               have r₂ := b8e136421
               grind)
            | exact resolve b8e137813 b8e136421
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e136421 b8e137813
          have b8e138024 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e137348
               have i₂ := b8e137830
               grind)
            | exact superpose b8e137830 b8e137348
            | exact resolve b8e137348 b8e137830
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137830
          have b8e138037 : x = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e138024
          have b8e138720 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e137348
               have i₂ := b8e138037
               grind)
            | exact superpose b8e138037 b8e137348
            | exact resolve b8e137348 b8e138037
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e137348 b8e138037
          have b8e138737 : x = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b8e138720
          have b8e138741 : x = (M.op x y) := by
            first
            | (have r₁ := b8e138737
               have r₂ := b8e21
               grind)
            | exact resolve b8e138737 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138737
          have b8e138959 : x ≠ y ∨ x = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e138741
               grind)
            | exact superpose b8e138741 b8e16
            | (have j0 := b8e16 y x
               grind)
            | exact resolve b8e16 b8e138741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e138960 : x ≠ x ∨ x = y ∨ y = (k y x) := by
            first
            | (have i₁ := b8e17 y x
               have i₂ := b8e138741
               grind)
            | exact superpose b8e138741 b8e17
            | (have j0 := b8e17 y x
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e138741
               grind)
            | exact resolve b8e17 b8e138741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e138977 : y = (k y x) ∨ x = y := by grind
          clear b8e138960
          have b8e139403 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e105 x y
               have i₂ := b8e138977
               grind)
            | exact superpose b8e138977 b8e105
            | (have j0 := b8e105 x y
               grind)
            | exact resolve b8e105 b8e138977
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e105
          have b8e139510 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e139403
          have b8e144708 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e139510
               grind)
            | exact superpose b8e139510 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e139510
               grind)
            | exact resolve b8e16 b8e139510
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139510
          have b8e144715 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
          clear b8e144708
          have b8e144718 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e144715
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e144715
            | exact resolve b8e144715 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144715
          have b8e145312 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e144718
               grind)
            | exact superpose b8e144718 b8e20
            | exact resolve b8e20 b8e144718
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e144718
          have b8e145328 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = y := by
            first
            | (have i₁ := b8e145312
               have i₂ := b8e138741
               grind)
            | exact superpose b8e138741 b8e145312
            | exact resolve b8e145312 b8e138741
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145312
          have b8e145329 : (σ x) = (σ (k y x)) ∨ x = y := by grind
          clear b8e145328
          have b8e145640 : (k y x) = (τ (σ x)) ∨ x = y := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e145329
               grind)
            | exact superpose b8e145329 b8e14
            | exact resolve b8e14 b8e145329
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145329
          have b8e145813 : x = (k y x) ∨ x = y := by
            first
            | (have i₁ := b8e145640
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e145640
            | exact resolve b8e145640 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e145640
          have b8e145814 : x = (k y x) := by
            first
            | (have r₁ := b8e145813
               have r₂ := b8e138959
               grind)
            | exact resolve b8e145813 b8e138959
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138959 b8e145813
          have b8e146113 : x = y ∨ x = y := by
            first
            | (have i₁ := b8e138977
               have i₂ := b8e145814
               grind)
            | exact superpose b8e145814 b8e138977
            | exact resolve b8e138977 b8e145814
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138977 b8e145814
          have b8e146228 : x = y := by grind
          clear b8e146113
          have b8e146515 : x ≠ (M.op x x) := by
            first
            | (have i₁ := b8e22
               have i₂ := b8e146228
               grind)
            | exact superpose b8e146228 b8e22
            | exact resolve b8e22 b8e146228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e146545 : x = (M.op x x) := by
            first
            | (have i₁ := b8e138741
               have i₂ := b8e146228
               grind)
            | exact superpose b8e146228 b8e138741
            | exact resolve b8e138741 b8e146228
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e138741 b8e146228
          have b8e146569 : False := by grind
          exact b8e146569

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_y_pyx_Equation1076 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
        intro X0 X1
        grind
      have b0e12 : ∀ X0 : G, (τ (σ X0)) = X0 := by
        intro X0
        grind
      have b0e13 : ∀ X0 : G, (σ (τ X0)) = X0 := by
        intro X0
        grind
      have b0e14 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
        intro X0 X1
        grind
      have b0e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
        intro X0 X1
        grind
      have b0e16 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        grind
      have b0e17 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
        intro X0 X1
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
      have b0e35 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op (M.op X0 (M.op X0 X1)) X1) = (k (M.op (M.op X0 (M.op X0 X1)) X1) X1) := by
        intro X0 X1
        first
        | (have i₁ := b0e14 (M.op (M.op X0 (M.op X0 X1)) X1) X1
           have i₂ := b0e11 X0 X1
           grind)
        | exact superpose b0e11 b0e14
        | (have j0 := b0e14 (M.op (M.op X0 (M.op X0 X1)) X1) X1
           grind)
        | (have r₁ := b0e14 (M.op (M.op X0 (M.op X0 X0)) X0) X0
           have r₂ := b0e11 X0 X0
           grind)
        | exact resolve b0e14 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e50 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op (τ X0) X1) := by
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
      have b0e51 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
      have b0e56 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
      have b0e81 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) X0) = (k (M.op (M.op X0 (M.op X0 X0)) X0) X0) := by
        intro X0
        first
        | (have j0 := b0e35 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e146 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e51 x y
           grind)
        | exact superpose b0e51 b0e18
        | (have j1 := b0e51 x y
           grind)
        | exact resolve b0e18 b0e51
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e153 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e154 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
        intro X0 X1
        first
        | (have j0 := b0e51 X0 X1
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e51
      have b0e453 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e50 (σ X0) X1
           have i₂ := b0e12 X0
           grind)
        | exact superpose b0e12 b0e50
        | exact resolve b0e50 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e50
      have b0e487 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e453 X0 X1
           have i₂ := b0e17 X1 X0
           grind)
        | exact superpose b0e17 b0e453
        | (have j0 := b0e453 X0 X1
           grind)
        | exact resolve b0e453 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e453
      have b0e639 : ∀ X0 : G, (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ≠ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have i₁ := b0e153 X0 (M.op (M.op X0 (M.op X0 X0)) X0)
           have i₂ := b0e81 X0
           grind)
        | exact superpose b0e81 b0e153
        | (have j0 := b0e153 X0 (M.op (M.op X0 (M.op X0 X0)) X0)
           grind)
        | exact resolve b0e153 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e643 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e153 (τ X1) (τ X0)
           have i₂ := b0e56 X1 X0
           grind)
        | exact superpose b0e56 b0e153
        | (have j0 := b0e153 (τ X1) (τ X0)
           grind)
        | exact resolve b0e153 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e653 : ∀ X0 : G, (σ (M.op (M.op X0 (M.op X0 X0)) X0)) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have j0 := b0e639 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e639
      have b0e658 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e643 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e643
        | (have j0 := b0e643 X0 X1
           grind)
        | exact resolve b0e643 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e643
      have b0e663 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e658 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e658
        | (have j0 := b0e658 X0 X1
           grind)
        | exact resolve b0e658 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e658
      have b0e667 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e663 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e663
        | (have j0 := b0e663 X0 X1
           grind)
        | exact resolve b0e663 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e663
      have b0e670 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e667 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e667
        | (have j0 := b0e667 X0 X1
           grind)
        | exact resolve b0e667 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e667
      have b0e673 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e670 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e670
        | (have j0 := b0e670 X0 X1
           grind)
        | exact resolve b0e670 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e670
      have b0e674 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e673 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e673
        | (have j0 := b0e673 X0 X1
           grind)
        | exact resolve b0e673 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e673
      have b0e692 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e154 (τ X1) (τ X0)
           have i₂ := b0e56 X1 X0
           grind)
        | exact superpose b0e56 b0e154
        | (have j0 := b0e154 (τ X1) (τ X0)
           grind)
        | exact resolve b0e154 b0e56
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e56 b0e154
      have b0e705 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e692 X0 X1
           have i₂ := b0e13 (k X0 X1)
           grind)
        | exact superpose b0e13 b0e692
        | (have j0 := b0e692 X0 X1
           grind)
        | exact resolve b0e692 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e692
      have b0e710 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e705 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e705
        | (have j0 := b0e705 X0 X1
           grind)
        | exact resolve b0e705 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e705
      have b0e714 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e710 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e710
        | (have j0 := b0e710 X0 X1
           grind)
        | exact resolve b0e710 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e710
      have b0e717 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
        intro X0 X1
        first
        | (have i₁ := b0e714 X0 X1
           have i₂ := b0e13 X1
           grind)
        | exact superpose b0e13 b0e714
        | (have j0 := b0e714 X0 X1
           grind)
        | exact resolve b0e714 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e714
      have b0e720 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e717 X0 X1
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e717
        | (have j0 := b0e717 X0 X1
           grind)
        | exact resolve b0e717 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e717
      have b0e721 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e720 X0 X0
           have i₂ := b0e13 X0
           grind)
        | exact superpose b0e13 b0e720
        | (have j0 := b0e720 X0 X1
           grind)
        | exact resolve b0e720 b0e13
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e720
      have b0e748 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e146
           have i₂ := b0e487 x y
           grind)
        | exact superpose b0e487 b0e146
        | (have j1 := b0e487 (σ x) (σ y)
           grind)
        | (have r₁ := b0e146
           have r₂ := b0e487 x y
           grind)
        | exact resolve b0e146 b0e487
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e146 b0e487
      have b0e749 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e748
      have b0e19087 : ∀ X0 : G, (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ≠ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ X0) = (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ X0) = (k (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have i₁ := b0e15 (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)
           have i₂ := b0e653 X0
           grind)
        | exact superpose b0e653 b0e15
        | (have j0 := b0e15 (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)
           have j1 := b0e653 X0
           grind)
        | (have r₁ := b0e15 (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)
           have r₂ := b0e653 X0
           grind)
        | exact resolve b0e15 b0e653
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e19104 : ∀ X0 : G, (σ X0) ≠ (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have j0 := b0e653 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e653
      have b0e19105 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ X0) = (k (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have j0 := b0e19087 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19087
      have b0e19109 : ∀ X0 : G, (σ X0) = (k (σ (M.op (M.op X0 (M.op X0 X0)) X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have j0 := b0e19105 X0
           have j1 := b0e19104 X0
           grind)
        | (have r₁ := b0e19105 X0
           have r₂ := b0e19104 X0
           grind)
        | exact resolve b0e19105 b0e19104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19105
      have b0e19112 : ∀ X0 : G, (σ X0) = (σ (k (M.op (M.op X0 (M.op X0 X0)) X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have i₁ := b0e19109 X0
           have i₂ := b0e17 (M.op (M.op X0 (M.op X0 X0)) X0) X0
           grind)
        | exact superpose b0e17 b0e19109
        | (have j0 := b0e19109 X0
           grind)
        | exact resolve b0e19109 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19109
      have b0e19115 : ∀ X0 : G, (σ X0) = (σ (M.op (M.op X0 (M.op X0 X0)) X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have i₁ := b0e19112 X0
           have i₂ := b0e81 X0
           grind)
        | exact superpose b0e81 b0e19112
        | (have j0 := b0e19112 X0
           grind)
        | exact resolve b0e19112 b0e81
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e81 b0e19112
      have b0e19116 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op (M.op X0 (M.op X0 X0)) X0))) := by
        intro X0
        first
        | (have j0 := b0e19115 X0
           have j1 := b0e19104 X0
           grind)
        | (have r₁ := b0e19115 X0
           have r₂ := b0e19104 X0
           grind)
        | exact resolve b0e19115 b0e19104
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19104 b0e19115
      have b0e40357 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e749
           grind)
        | exact superpose b0e749 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 (σ y) (σ x)
           have r₂ := b0e749
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e749
           grind)
        | exact resolve b0e14 b0e749
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e749
      have b0e40376 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e40357
      have b0e40393 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e40376
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e40376
        | exact resolve b0e40376 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40376
      have b0e41570 : (σ x) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e14 (σ y) (σ x)
           have i₂ := b0e40393
           grind)
        | exact superpose b0e40393 b0e14
        | (have j0 := b0e14 (σ y) (σ x)
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e40393
           grind)
        | exact resolve b0e14 b0e40393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e41571 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e40393
           grind)
        | exact superpose b0e40393 b0e15
        | (have j0 := b0e15 y x
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e40393
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e40393
           grind)
        | exact resolve b0e15 b0e40393
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e40393
      have b0e41589 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e41571
      have b0e41605 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e41589
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e41589
        | exact resolve b0e41589 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41589
      have b0e41606 : (σ y) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e41570
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e41570
        | exact resolve b0e41570 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41570
      have b0e41607 : (σ x) ≠ (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
      clear b0e41606
      have b0e142196 : (k y x) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e41605
           grind)
        | exact superpose b0e41605 b0e12
        | exact resolve b0e12 b0e41605
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41605
      have b0e142237 : (k y x) = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have r₁ := b0e142196
           have r₂ := b0e41607
           grind)
        | exact resolve b0e142196 b0e41607
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e41607 b0e142196
      have b0e142255 : x = (k y x) ∨ (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e142237
           have i₂ := b0e12 x
           grind)
        | exact superpose b0e12 b0e142237
        | exact resolve b0e142237 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142237
      have b0e142256 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have j1 := b0e721 y x
           grind)
        | (have r₁ := b0e142255
           have r₂ := b0e721 y x
           grind)
        | exact resolve b0e142255 b0e721
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e721 b0e142255
      have b0e142313 : (k y x) = (τ (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e12 (k y x)
           have i₂ := b0e142256
           grind)
        | exact superpose b0e142256 b0e12
        | exact resolve b0e12 b0e142256
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142256
      have b0e142487 : y = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
        first
        | (have i₁ := b0e142313
           have i₂ := b0e12 y
           grind)
        | exact superpose b0e12 b0e142313
        | exact resolve b0e142313 b0e12
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142313
      have b0e142488 : x = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have j1 := b0e674 y x
           grind)
        | (have r₁ := b0e142487
           have r₂ := b0e674 y x
           grind)
        | exact resolve b0e142487 b0e674
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e674 b0e142487
      have b0e142522 : x ≠ x ∨ y = (k y x) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e14 y x
           have i₂ := b0e142488
           grind)
        | exact superpose b0e142488 b0e14
        | (have j0 := b0e14 y x
           grind)
        | (have r₁ := b0e14 y x
           have r₂ := b0e142488
           grind)
        | exact resolve b0e14 b0e142488
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e142538 : x ≠ y ∨ y = (M.op x y) := by grind
      have b0e142539 : y = (k y x) ∨ y = (M.op x y) := by grind
      clear b0e142522
      have b0e143079 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e153 x y
           have i₂ := b0e142539
           grind)
        | exact superpose b0e142539 b0e153
        | (have j0 := b0e153 x y
           grind)
        | exact resolve b0e153 b0e142539
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e153
      have b0e143310 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
      clear b0e143079
      have b0e147983 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e143310
           grind)
        | exact superpose b0e143310 b0e18
        | exact resolve b0e18 b0e143310
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e143310
      have b0e148438 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e147983
           have i₂ := b0e142488
           grind)
        | exact superpose b0e142488 b0e147983
        | exact resolve b0e147983 b0e142488
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e147983
      have b0e148441 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
      clear b0e148438
      have b0e148442 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e148441
           have r₂ := b0e142538
           grind)
        | exact resolve b0e148441 b0e142538
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148441
      have b0e148673 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e148442
           grind)
        | exact superpose b0e148442 b0e18
        | exact resolve b0e18 b0e148442
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e148681 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e15 (σ y) (σ x)
           have i₂ := b0e148442
           grind)
        | exact superpose b0e148442 b0e15
        | (have j0 := b0e15 (σ y) (σ x)
           grind)
        | (have r₁ := b0e15 (σ y) (σ x)
           have r₂ := b0e148442
           grind)
        | (have r₁ := b0e15 y x
           have r₂ := b0e148442
           grind)
        | exact resolve b0e15 b0e148442
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148442
      have b0e148695 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
      clear b0e148681
      have b0e148700 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e148695
           have i₂ := b0e17 y x
           grind)
        | exact superpose b0e17 b0e148695
        | exact resolve b0e148695 b0e17
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148695
      have b0e148929 : (σ x) ≠ (σ y) ∨ x = y ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e148673
           have i₂ := b0e142488
           grind)
        | exact superpose b0e142488 b0e148673
        | exact resolve b0e148673 b0e142488
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142488 b0e148673
      have b0e148933 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by
        first
        | (have r₁ := b0e148929
           have r₂ := b0e142538
           grind)
        | exact resolve b0e148929 b0e142538
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142538 b0e148929
      have b0e148958 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
        first
        | (have i₁ := b0e148700
           have i₂ := b0e142539
           grind)
        | exact superpose b0e142539 b0e148700
        | exact resolve b0e148700 b0e142539
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e142539 b0e148700
      have b0e149106 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
      clear b0e148958
      have b0e149203 : y = (M.op x y) := by
        first
        | (have r₁ := b0e149106
           have r₂ := b0e148933
           grind)
        | exact resolve b0e149106 b0e148933
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e148933 b0e149106
      have b0e149482 : x = (M.op y (M.op (M.op x y) y)) := by
        first
        | (have i₁ := b0e11 x y
           have i₂ := b0e149203
           grind)
        | exact superpose b0e149203 b0e11
        | exact resolve b0e11 b0e149203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149520 : x = (M.op y (M.op y y)) := by
        first
        | (have i₁ := b0e149482
           have i₂ := b0e149203
           grind)
        | exact superpose b0e149203 b0e149482
        | exact resolve b0e149482 b0e149203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149482
      have b0e149573 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
        first
        | (have i₁ := b0e19116 y
           have i₂ := b0e149520
           grind)
        | exact superpose b0e149520 b0e19116
        | exact resolve b0e19116 b0e149520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e19116
      have b0e149577 : y = (M.op y (M.op x y)) := by
        first
        | (have i₁ := b0e11 y y
           have i₂ := b0e149520
           grind)
        | exact superpose b0e149520 b0e11
        | exact resolve b0e11 b0e149520
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e149615 : y = (M.op y y) := by
        first
        | (have i₁ := b0e149577
           have i₂ := b0e149203
           grind)
        | exact superpose b0e149203 b0e149577
        | exact resolve b0e149577 b0e149203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149577
      have b0e149619 : (σ y) = (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e149573
           have i₂ := b0e149203
           grind)
        | exact superpose b0e149203 b0e149573
        | exact resolve b0e149573 b0e149203
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149203 b0e149573
      have b0e149688 : x = (M.op y y) := by
        first
        | (have i₁ := b0e149520
           have i₂ := b0e149615
           grind)
        | exact superpose b0e149615 b0e149520
        | exact resolve b0e149520 b0e149615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149520
      have b0e149716 : x = y := by
        first
        | (have i₁ := b0e149688
           have i₂ := b0e149615
           grind)
        | exact superpose b0e149615 b0e149688
        | exact resolve b0e149688 b0e149615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149688
      have b0e149793 : (M.op (σ y) (σ y)) ≠ (σ (M.op y y)) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e149716
           grind)
        | exact superpose b0e149716 b0e18
        | exact resolve b0e18 b0e149716
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149716
      have b0e149927 : (σ y) ≠ (M.op (σ y) (σ y)) := by
        first
        | (have i₁ := b0e149793
           have i₂ := b0e149615
           grind)
        | exact superpose b0e149615 b0e149793
        | exact resolve b0e149793 b0e149615
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e149615 b0e149793
      have b0e149943 : False := by grind
      exact b0e149943
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
        have b1e26 : x = (k x y) := by grind
        clear b1e24
        have b1e37 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e39 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e37
        have b1e40 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e39
             have r₂ := b1e23
             grind)
          | exact resolve b1e39 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e39
        have b1e41 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e40
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e40
          | exact resolve b1e40 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e40
        have b1e42 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e41
             have i₂ := b1e26
             grind)
          | exact superpose b1e26 b1e41
          | exact resolve b1e41 b1e26
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e26 b1e41
        have b1e43 : False := by grind
        exact b1e43
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e23 : y ≠ y ∨ x = (k x y) := by
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
        have b2e24 : x = (k x y) := by grind
        clear b2e23
        have b2e40 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e120 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e40 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e40
        have b2e506 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have i₁ := b2e120 y x
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e120
          | (have j0 := b2e120 y x
             grind)
          | exact resolve b2e120 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e120
        have b2e510 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
        clear b2e506
        have b2e514 : (σ y) = (M.op (σ y) (σ x)) := by
          first
          | (have r₁ := b2e510
             have r₂ := b2e22
             grind)
          | exact resolve b2e510 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e510
        have b2e518 : False := by grind
        exact b2e518
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y x) := by grind
        have b3e21 : x = (M.op y x) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
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
        have b3e27 : (σ x) = (σ (k x y)) := by
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
        have b3e28 : (k x y) = (τ (σ x)) := by
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
        have b3e29 : x = (k x y) := by
          first
          | (have i₁ := b3e28
             have i₂ := b3e13 x
             grind)
          | exact superpose b3e13 b3e28
          | exact resolve b3e28 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e28
        have b3e51 : x ≠ x ∨ x = y ∨ y = (k x y) := by
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
        have b3e52 : x = y ∨ y = (k x y) := by grind
        clear b3e51
        have b3e53 : y = (k x y) := by
          first
          | (have r₁ := b3e52
             have r₂ := b3e23
             grind)
          | exact resolve b3e52 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e52
        have b3e57 : x = y := by
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
        have b3e59 : False := by grind
        exact b3e59
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b4e21 : y ≠ (M.op y x) := by grind
          have b4e22 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
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
          have b4e31 : y = (M.op x (M.op (M.op y x) x)) := by
            first
            | (have i₁ := b4e13 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e31
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e31
            | exact resolve b4e31 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31
          have b4e37 : x = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : x = (M.op x x) := by
            first
            | (have i₁ := b4e37
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e37
            | exact resolve b4e37 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e37
          have b4e58 : y = (M.op x x) := by
            first
            | (have i₁ := b4e36
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e36
            | exact resolve b4e36 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e63 : x = y := by
            first
            | (have i₁ := b4e58
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e58
            | exact resolve b4e58 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e58
          have b4e65 : False := by grind
          exact b4e65
        · have b5e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y x) := by grind
          have b5e22 : x = (M.op y x) := by grind
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
          have b5e29 : y = (M.op x (M.op (M.op y x) x)) := by
            first
            | (have i₁ := b5e13 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e32 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e29
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e29
            | exact resolve b5e29 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e29
          have b5e33 : x = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b5e13 x x
               have i₂ := b5e32
               grind)
            | exact superpose b5e32 b5e13
            | exact resolve b5e13 b5e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : x = (M.op x x) := by
            first
            | (have i₁ := b5e33
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e33
            | exact resolve b5e33 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e33
          have b5e50 : y = (M.op x x) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e32
            | exact resolve b5e32 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e55 : x = y := by
            first
            | (have i₁ := b5e50
               have i₂ := b5e36
               grind)
            | exact superpose b5e36 b5e50
            | exact resolve b5e50 b5e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e50
          have b5e57 : False := by grind
          exact b5e57
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y x) := by grind
        have b6e21 : x ≠ (M.op y x) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e23 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b6e24 : (σ x) = (k (σ x) (σ y)) := by grind
        clear b6e23
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
        have b6e66 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
        have b6e68 : x = (M.op y x) ∨ y = (M.op y x) := by grind
        clear b6e66
        have b6e71 : y = (M.op y x) := by
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y x) := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
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
          have b7e55 : y = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op y x) := by
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
          have b7e56 : y = (M.op y x) ∨ x = (M.op y x) := by grind
          clear b7e55
          have b7e58 : x = (M.op y x) := by
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
        · have b8e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e22 : x ≠ (M.op y x) := by grind
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
          have b8e43 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e113 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e120 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e121 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b8e43 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e43
          have b8e383 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e120 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e120
            | (have j0 := b8e120 (τ X1) (τ X0)
               grind)
            | exact resolve b8e120 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e391 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e383 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e383
            | (have j0 := b8e383 X0 X1
               grind)
            | exact resolve b8e383 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e383
          have b8e394 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e391 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e391
            | (have j0 := b8e391 X0 X1
               grind)
            | exact resolve b8e391 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e391
          have b8e396 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
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
          have b8e397 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e396 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e396
            | (have j0 := b8e396 X0 X1
               grind)
            | exact resolve b8e396 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e396
          have b8e398 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X0 := by
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
          have b8e399 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e398 X0 X0
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
          have b8e449 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e121 (τ X1) (τ X0)
               have i₂ := b8e46 X1 X0
               grind)
            | exact superpose b8e46 b8e121
            | (have j0 := b8e121 (τ X1) (τ X0)
               grind)
            | exact resolve b8e121 b8e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e46 b8e121
          have b8e456 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e449 X0 X1
               have i₂ := b8e15 (k X0 X1)
               grind)
            | exact superpose b8e15 b8e449
            | (have j0 := b8e449 X0 X1
               grind)
            | exact resolve b8e449 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e449
          have b8e459 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e456 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e456
            | (have j0 := b8e456 X0 X1
               grind)
            | exact resolve b8e456 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e456
          have b8e461 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e459 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e459
            | (have j0 := b8e459 X0 X1
               grind)
            | exact resolve b8e459 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e459
          have b8e462 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e461 X0 X1
               have i₂ := b8e15 X1
               grind)
            | exact superpose b8e15 b8e461
            | (have j0 := b8e461 X0 X1
               grind)
            | exact resolve b8e461 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e461
          have b8e463 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e462 X0 X1
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e462
            | (have j0 := b8e462 X0 X1
               grind)
            | exact resolve b8e462 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e462
          have b8e464 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e463 X0 X0
               have i₂ := b8e15 X0
               grind)
            | exact superpose b8e15 b8e463
            | (have j0 := b8e463 X0 X1
               grind)
            | exact resolve b8e463 b8e15
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e463
          have b8e475 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e113
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e113
            | (have j1 := b8e18 (σ y) (σ x)
               grind)
            | exact resolve b8e113 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e476 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e475
          have b8e3738 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e476
               grind)
            | exact superpose b8e476 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e476
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e476
               grind)
            | exact resolve b8e17 b8e476
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3754 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e476
          have b8e3755 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e3738
          have b8e3757 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e3755
               have r₂ := b8e3754
               grind)
            | exact resolve b8e3755 b8e3754
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3754 b8e3755
          have b8e3761 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e3757
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e3757
            | exact resolve b8e3757 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3757
          have b8e22678 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e16 (σ y) (σ x)
               have i₂ := b8e3761
               grind)
            | exact superpose b8e3761 b8e16
            | (have j0 := b8e16 (σ y) (σ x)
               grind)
            | (have r₁ := b8e16 (σ y) (σ x)
               have r₂ := b8e3761
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e3761
               grind)
            | exact resolve b8e16 b8e3761
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3761
          have b8e22695 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e22678
          have b8e22704 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e22695
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e22695
            | exact resolve b8e22695 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22695
          have b8e23082 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e22704
               grind)
            | exact superpose b8e22704 b8e14
            | exact resolve b8e14 b8e22704
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e22704
          have b8e23242 : y = (k y x) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e23082
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e23082
            | exact resolve b8e23082 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23082
          have b8e23245 : (σ x) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e399 y x
               grind)
            | (have r₁ := b8e23242
               have r₂ := b8e399 y x
               grind)
            | exact resolve b8e23242 b8e399
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e399 b8e23242
          have b8e23370 : (k y x) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e14 (k y x)
               have i₂ := b8e23245
               grind)
            | exact superpose b8e23245 b8e14
            | exact resolve b8e14 b8e23245
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23245
          have b8e23531 : x = (k y x) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e23370
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e23370
            | exact resolve b8e23370 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23370
          have b8e23532 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have j1 := b8e464 y x
               grind)
            | (have r₁ := b8e23531
               have r₂ := b8e464 y x
               grind)
            | exact resolve b8e23531 b8e464
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e464 b8e23531
          have b8e23783 : x = (M.op y (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e13 x y
               have i₂ := b8e23532
               grind)
            | exact superpose b8e23532 b8e13
            | exact resolve b8e13 b8e23532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e23802 : x ≠ y ∨ x = (M.op x y) := by grind
          have b8e24614 : x = (M.op y (M.op y y)) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e23783
               have i₂ := b8e23532
               grind)
            | exact superpose b8e23532 b8e23783
            | exact resolve b8e23783 b8e23532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23783
          have b8e24638 : x = (M.op y (M.op y y)) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e24614
               have r₂ := b8e23802
               grind)
            | exact resolve b8e24614 b8e23802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24614
          have b8e24742 : y = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e13 y y
               have i₂ := b8e24638
               grind)
            | exact superpose b8e24638 b8e13
            | exact resolve b8e13 b8e24638
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e24881 : y = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24742
               have i₂ := b8e23532
               grind)
            | exact superpose b8e23532 b8e24742
            | exact resolve b8e24742 b8e23532
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23532 b8e24742
          have b8e24907 : y = (M.op y y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b8e24881
               have r₂ := b8e23802
               grind)
            | exact resolve b8e24881 b8e23802
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e23802 b8e24881
          have b8e25144 : x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24638
               have i₂ := b8e24907
               grind)
            | exact superpose b8e24907 b8e24638
            | exact resolve b8e24638 b8e24907
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24907
          have b8e25166 : x = (M.op y y) ∨ x = (M.op x y) := by grind
          clear b8e25144
          have b8e25737 : x = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e24638
               have i₂ := b8e25166
               grind)
            | exact superpose b8e25166 b8e24638
            | exact resolve b8e24638 b8e25166
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e24638 b8e25166
          have b8e25763 : x = (M.op y x) ∨ x = (M.op x y) := by grind
          clear b8e25737
          have b8e25767 : x = (M.op x y) := by
            first
            | (have r₁ := b8e25763
               have r₂ := b8e22
               grind)
            | exact resolve b8e25763 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25763
          have b8e26040 : x ≠ x ∨ y = (k y x) := by
            first
            | (have i₁ := b8e16 y x
               have i₂ := b8e25767
               grind)
            | exact superpose b8e25767 b8e16
            | (have j0 := b8e16 y x
               grind)
            | (have r₁ := b8e16 y x
               have r₂ := b8e25767
               grind)
            | exact resolve b8e16 b8e25767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e26057 : y = (k y x) := by grind
          clear b8e26040
          have b8e26238 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e120 x y
               have i₂ := b8e26057
               grind)
            | exact superpose b8e26057 b8e120
            | (have j0 := b8e120 x y
               grind)
            | exact resolve b8e120 b8e26057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e120
          have b8e26266 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e26238
          have b8e30998 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e26266
               grind)
            | exact superpose b8e26266 b8e17
            | (have j0 := b8e17 (σ y) (σ x)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e26266
               grind)
            | exact resolve b8e17 b8e26266
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e31015 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e26266
          have b8e31016 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b8e30998
          have b8e31019 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e31016
               have r₂ := b8e31015
               grind)
            | exact resolve b8e31016 b8e31015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31016
          have b8e31028 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e31019
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e31019
            | exact resolve b8e31019 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31019
          have b8e31036 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e31028
               have i₂ := b8e26057
               grind)
            | exact superpose b8e26057 b8e31028
            | exact resolve b8e31028 b8e26057
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e26057 b8e31028
          have b8e31041 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e31036
               have r₂ := b8e31015
               grind)
            | exact resolve b8e31036 b8e31015
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31015 b8e31036
          have b8e31114 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e31041
               grind)
            | exact superpose b8e31041 b8e20
            | exact resolve b8e20 b8e31041
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31041
          have b8e31153 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b8e31114
               have i₂ := b8e25767
               grind)
            | exact superpose b8e25767 b8e31114
            | exact resolve b8e31114 b8e25767
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e25767 b8e31114
          have b8e31154 : False := by grind
          exact b8e31154

/-- `Equation1076`: `x = y ◇ ((x ◇ (x ◇ y)) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation1076 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1076 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1076.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e57 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e28
      have b0e59 : False := by grind
      exact b0e59
    · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y x) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : y = (M.op x (M.op (M.op y x) x)) := by
            first
            | (have i₁ := b4e13 y x
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e36 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b4e32
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e32
            | exact resolve b4e32 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e38 : x = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b4e13 x x
               have i₂ := b4e36
               grind)
            | exact superpose b4e36 b4e13
            | exact resolve b4e13 b4e36
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e40 : x = (M.op x x) := by
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
          have b4e56 : y = (M.op x x) := by
            first
            | (have i₁ := b4e36
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e36
            | exact resolve b4e36 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e36
          have b4e59 : x = y := by
            first
            | (have i₁ := b4e56
               have i₂ := b4e40
               grind)
            | exact superpose b4e40 b4e56
            | exact resolve b4e56 b4e40
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e40 b4e56
          have b4e61 : False := by grind
          exact b4e61
        · have b5e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b5e21 : x ≠ y := by grind
          have b5e22 : x = (M.op y x) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : y = (M.op x (M.op (M.op y x) x)) := by
            first
            | (have i₁ := b5e13 y x
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e34 : y = (M.op x (M.op x x)) := by
            first
            | (have i₁ := b5e32
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e32
            | exact resolve b5e32 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e35 : x = (M.op x (M.op y x)) := by
            first
            | (have i₁ := b5e13 x x
               have i₂ := b5e34
               grind)
            | exact superpose b5e34 b5e13
            | exact resolve b5e13 b5e34
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e37 : x = (M.op x x) := by
            first
            | (have i₁ := b5e35
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e35
            | exact resolve b5e35 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35
          have b5e49 : y = (M.op x x) := by
            first
            | (have i₁ := b5e34
               have i₂ := b5e37
               grind)
            | exact superpose b5e37 b5e34
            | exact resolve b5e34 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e34
          have b5e52 : x = y := by
            first
            | (have i₁ := b5e49
               have i₂ := b5e37
               grind)
            | exact superpose b5e37 b5e49
            | exact resolve b5e49 b5e37
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e37 b5e49
          have b5e54 : False := by grind
          exact b5e54
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
      · rcases eq_or_ne (M.op (σ y) (σ x)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : x ≠ y := by grind
          have b7e22 : x ≠ (M.op y x) := by grind
          have b7e23 : (σ x) ≠ (σ y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e43 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e43
          have b7e46 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e45
               have r₂ := b7e23
               grind)
            | exact resolve b7e45 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e45
          have b7e47 : (σ x) = (σ (k x y)) := by
            first
            | (have i₁ := b7e46
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e46
            | exact resolve b7e46 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e46
          have b7e50 : (k x y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e47
               grind)
            | exact superpose b7e47 b7e14
            | exact resolve b7e14 b7e47
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e47
          have b7e51 : x = (k x y) := by
            first
            | (have i₁ := b7e50
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e50
            | exact resolve b7e50 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e50
          have b7e61 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = y := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e51
               grind)
            | exact superpose b7e51 b7e18
            | (have j0 := b7e18 x y
               grind)
            | exact resolve b7e18 b7e51
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e51
          have b7e62 : x = (M.op y x) ∨ x = y := by grind
          clear b7e61
          have b7e64 : x = y := by
            first
            | (have r₁ := b7e62
               have r₂ := b7e22
               grind)
            | exact resolve b7e62 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e62
          have b7e66 : False := by grind
          exact b7e66
        · have b8e13 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X0 (M.op X0 X1)) X1)) = X0 := by
            intro X0 X1
            grind
          have b8e17 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e32 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op X0 X1)) X1) (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X1)) X1))) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (M.op (M.op X0 (M.op X0 X1)) X1)
               have i₂ := b8e13 X0 X1
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e54 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
          have b8e88 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
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
          have b8e96 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e88
               have r₂ := b8e23
               grind)
            | exact resolve b8e88 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e88
          have b8e342 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e96
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e96
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e96
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e96
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e96 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e96
          have b8e343 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e342
          have b8e344 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e343
               have r₂ := b8e21
               grind)
            | exact resolve b8e343 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e343
          have b8e346 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e344
               grind)
            | exact superpose b8e344 b8e20
            | exact resolve b8e20 b8e344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e350 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e17 (σ y) (σ x)
               have i₂ := b8e344
               grind)
            | exact superpose b8e344 b8e17
            | (have j0 := b8e17 (σ x) (σ y)
               grind)
            | (have r₁ := b8e17 (σ y) (σ x)
               have r₂ := b8e344
               grind)
            | (have r₁ := b8e17 y x
               have r₂ := b8e344
               grind)
            | exact resolve b8e17 b8e344
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e344
          have b8e352 : (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
          clear b8e350
          have b8e353 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
            first
            | (have r₁ := b8e352
               have r₂ := b8e23
               grind)
            | exact resolve b8e352 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e352
          have b8e355 : (σ y) = (σ (k y x)) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e353
               have i₂ := b8e19 y x
               grind)
            | exact superpose b8e19 b8e353
            | exact resolve b8e353 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e353
          have b8e420 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
            first
            | (have i₁ := b8e355
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e355
            | (have j1 := b8e18 y x
               grind)
            | exact resolve b8e355 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e355
          have b8e440 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
          clear b8e420
          have b8e456 : y = (M.op x y) ∨ x = y := by
            first
            | (have r₁ := b8e440
               have r₂ := b8e346
               grind)
            | exact resolve b8e440 b8e346
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e346 b8e440
          have b8e457 : y = (M.op x y) := by
            first
            | (have r₁ := b8e456
               have r₂ := b8e21
               grind)
            | exact resolve b8e456 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e456
          have b8e499 : x = (M.op y (M.op (M.op x y) y)) := by
            first
            | (have i₁ := b8e13 x y
               have i₂ := b8e457
               grind)
            | exact superpose b8e457 b8e13
            | exact resolve b8e13 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e501 : x = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b8e499
               have i₂ := b8e457
               grind)
            | exact superpose b8e457 b8e499
            | exact resolve b8e499 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e499
          have b8e576 : y = (M.op (M.op x y) (M.op (M.op y y) (M.op x y))) := by
            first
            | (have i₁ := b8e32 y y
               have i₂ := b8e501
               grind)
            | exact superpose b8e501 b8e32
            | exact resolve b8e32 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e32
          have b8e577 : y = (M.op y (M.op x y)) := by
            first
            | (have i₁ := b8e13 y y
               have i₂ := b8e501
               grind)
            | exact superpose b8e501 b8e13
            | exact resolve b8e13 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e583 : y = (M.op y y) := by
            first
            | (have i₁ := b8e577
               have i₂ := b8e457
               grind)
            | exact superpose b8e457 b8e577
            | exact resolve b8e577 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e577
          have b8e584 : y = (M.op y (M.op (M.op y y) y)) := by
            first
            | (have i₁ := b8e576
               have i₂ := b8e457
               grind)
            | exact superpose b8e457 b8e576
            | exact resolve b8e576 b8e457
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e457 b8e576
          have b8e585 : y = (M.op y (M.op y y)) := by
            first
            | (have i₁ := b8e584
               have i₂ := b8e583
               grind)
            | exact superpose b8e583 b8e584
            | exact resolve b8e584 b8e583
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e583 b8e584
          have b8e586 : x = y := by
            first
            | (have i₁ := b8e585
               have i₂ := b8e501
               grind)
            | exact superpose b8e501 b8e585
            | exact resolve b8e585 b8e501
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e501 b8e585
          have b8e587 : False := by grind
          exact b8e587

/-- `Equation1286`: `x = y ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_pyy_pyy_pxx_pxy_Equation1286 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1286 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1286.models_iff G M).mp hM
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
      have b0e43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
        intro X0
        first
        | (have j0 := b0e14 X0 X0
           grind)
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
      have b0e54 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
        intro X0
        first
        | (have i₁ := b0e49 X0
           have i₂ := b0e43 X0
           grind)
        | exact superpose b0e43 b0e49
        | exact resolve b0e49 b0e43
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e43 b0e49
      have b0e180 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
        first
        | (have i₁ := b0e22
           have i₂ := b0e54 x
           grind)
        | exact superpose b0e54 b0e22
        | (have r₁ := b0e22
           have r₂ := b0e54 x
           grind)
        | exact resolve b0e22 b0e54
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e22 b0e54
      have b0e189 : False := by grind
      exact b0e189
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
        have b1e49 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b1e53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b1e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by grind
        clear b1e51
        have b1e55 : (k x y) = (M.op y y) := by grind
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
        have b1e74 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
        have b1e124 : (σ (M.op x x)) ≠ (σ (M.op y y)) := by
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
        have b1e608 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e74 (σ x)
             have i₂ := b1e57
             grind)
          | exact superpose b1e57 b1e74
          | (have j0 := b1e74 (σ x)
             grind)
          | (have r₁ := b1e74 (σ x)
             have r₂ := b1e57
             grind)
          | exact resolve b1e74 b1e57
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e57 b1e74
        have b1e609 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
        clear b1e608
        have b1e610 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have i₁ := b1e609
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e609
          | exact resolve b1e609 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e609
        have b1e611 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e610
             have r₂ := b1e124
             grind)
          | exact resolve b1e610 b1e124
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e610
        have b1e612 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
          first
          | (have i₁ := b1e611
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e611
          | exact resolve b1e611 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e611
        have b1e613 : (M.op (σ x) (σ x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e612
             have i₂ := b1e55
             grind)
          | exact superpose b1e55 b1e612
          | exact resolve b1e612 b1e55
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e55 b1e612
        have b1e614 : (σ (M.op x x)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b1e613
             have i₂ := b1e66 x
             grind)
          | exact superpose b1e66 b1e613
          | exact resolve b1e613 b1e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e66 b1e613
        have b1e615 : False := by grind
        exact b1e615
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
        have b2e48 : (M.op x x) ≠ (M.op x x) ∨ (k x y) = (M.op y y) := by
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
        have b2e51 : (k x y) = (M.op y y) := by grind
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
        have b2e135 : (M.op (σ x) (σ y)) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e22
             have i₂ := b2e60 y
             grind)
          | exact superpose b2e60 b2e22
          | exact resolve b2e22 b2e60
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e60
        have b2e956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have j0 := b2e87 (σ x)
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e87
        have b2e957 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b2e956
             have r₂ := b2e21
             grind)
          | exact resolve b2e956 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e956
        have b2e958 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
          first
          | (have i₁ := b2e957
             have i₂ := b2e18 x y
             grind)
          | exact superpose b2e18 b2e957
          | exact resolve b2e957 b2e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e957
        have b2e959 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b2e958
             have i₂ := b2e51
             grind)
          | exact superpose b2e51 b2e958
          | exact resolve b2e958 b2e51
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51 b2e958
        have b2e960 : False := by grind
        exact b2e960
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
        have b3e51 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b3e54 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b3e51
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
        have b3e59 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
          intro X0
          first
          | (have i₁ := b3e18 X0 X0
             have i₂ := b3e53 (σ X0)
             grind)
          | exact superpose b3e53 b3e18
          | exact resolve b3e18 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e66 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
          intro X0
          first
          | (have i₁ := b3e59 X0
             have i₂ := b3e53 X0
             grind)
          | exact superpose b3e53 b3e59
          | exact resolve b3e59 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e59
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
        have b3e76 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
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
        have b3e78 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b3e76
        have b3e79 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b3e78
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e78
          | exact resolve b3e78 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e78
        have b3e80 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b3e79
             have i₂ := b3e53 y
             grind)
          | exact superpose b3e53 b3e79
          | exact resolve b3e79 b3e53
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e53 b3e79
        have b3e81 : (σ (M.op x y)) = (σ (k x y)) := by
          first
          | (have i₁ := b3e80
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e80
          | exact resolve b3e80 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e80
        have b3e185 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b3e23
             have i₂ := b3e66 x
             grind)
          | exact superpose b3e66 b3e23
          | exact resolve b3e23 b3e66
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e66
        have b3e220 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
          first
          | (have j0 := b3e72 x
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e72
        have b3e221 : (M.op x x) = (k x y) := by
          first
          | (have r₁ := b3e220
             have r₂ := b3e20
             grind)
          | exact resolve b3e220 b3e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e220
        have b3e225 : (σ (M.op x y)) = (σ (M.op x x)) := by
          first
          | (have i₁ := b3e81
             have i₂ := b3e221
             grind)
          | exact superpose b3e221 b3e81
          | exact resolve b3e81 b3e221
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e81 b3e221
        have b3e229 : False := by grind
        exact b3e229
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
          have b4e64 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b4e64
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
          have b5e64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b5e16 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
            intro X0
            first
            | (have i₁ := b5e19 X0 X0
               have i₂ := b5e64 (σ X0)
               grind)
            | exact superpose b5e64 b5e19
            | exact resolve b5e19 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b5e68 X0
               have i₂ := b5e64 X0
               grind)
            | exact superpose b5e64 b5e68
            | exact resolve b5e68 b5e64
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e64 b5e68
          have b5e85 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (M.op X0 y) ∨ (M.op X0 X0) = (k X0 y) := by
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
          have b5e120 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b5e247 : (M.op x y) = (M.op x x) ∨ (M.op x x) = (k x y) := by
            first
            | (have j0 := b5e85 x
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e85
          have b5e248 : (M.op x x) = (k x y) := by
            first
            | (have r₁ := b5e247
               have r₂ := b5e21
               grind)
            | exact resolve b5e247 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e247
          have b5e1198 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e120 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e120
          have b5e1199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1198
               have r₂ := b5e23
               grind)
            | exact resolve b5e1198 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1198
          have b5e1200 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e1199
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e1199
            | exact resolve b5e1199 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1199
          have b5e1201 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
            first
            | (have i₁ := b5e1200
               have i₂ := b5e248
               grind)
            | exact superpose b5e248 b5e1200
            | exact resolve b5e1200 b5e248
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e248 b5e1200
          have b5e1204 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e1201
               grind)
            | exact superpose b5e1201 b5e23
            | exact resolve b5e23 b5e1201
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1201
          have b5e1214 : False := by grind
          exact b5e1214
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
        have b6e49 : (M.op (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
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
        have b6e50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
          intro X0
          first
          | (have j0 := b6e15 X0 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e51 : (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
        clear b6e49
        have b6e52 : (M.op (σ y) (σ y)) = (σ (k x y)) := by
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
        have b6e70 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ (k x y)) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e15 (σ y) (σ y)
             have i₂ := b6e52
             grind)
          | exact superpose b6e52 b6e15
          | exact resolve b6e15 b6e52
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e52
        have b6e72 : (σ (k x y)) = (k (σ y) (σ y)) := by grind
        clear b6e70
        have b6e73 : (σ (k x y)) = (σ (k y y)) := by
          first
          | (have i₁ := b6e72
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e72
          | exact resolve b6e72 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e72
        have b6e74 : (σ (k x y)) = (σ (M.op y y)) := by
          first
          | (have i₁ := b6e73
             have i₂ := b6e50 y
             grind)
          | exact superpose b6e50 b6e73
          | exact resolve b6e73 b6e50
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e50 b6e73
        have b6e125 : (k x y) = (τ (σ (M.op y y))) := by
          first
          | (have i₁ := b6e13 (k x y)
             have i₂ := b6e74
             grind)
          | exact superpose b6e74 b6e13
          | exact resolve b6e13 b6e74
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e74
        have b6e126 : (M.op y y) = (k x y) := by
          first
          | (have i₁ := b6e125
             have i₂ := b6e13 (M.op y y)
             grind)
          | exact superpose b6e13 b6e125
          | exact resolve b6e125 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e125
        have b6e144 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
          first
          | (have i₁ := b6e17 x y
             have i₂ := b6e126
             grind)
          | exact superpose b6e126 b6e17
          | (have j0 := b6e17 x y
             grind)
          | exact resolve b6e17 b6e126
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e126
        have b6e145 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
        clear b6e144
        have b6e147 : (M.op x y) = (M.op x x) := by
          first
          | (have r₁ := b6e145
             have r₂ := b6e21
             grind)
          | exact resolve b6e145 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e145
        have b6e149 : False := by grind
        exact b6e149
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
          have b7e62 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
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
          clear b7e62
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
          have b7e86 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
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
          have b7e88 : ∀ X0 : G, (σ (M.op y y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
            intro X0
            first
            | (have i₁ := b7e86 X0
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e86
            | (have j0 := b7e86 X0
               grind)
            | exact resolve b7e86 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : (M.op (σ x) (σ x)) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b7e23
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e23
            | exact resolve b7e23 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e94 : (σ (M.op y y)) ≠ (σ (M.op x x)) := by
            first
            | (have i₁ := b7e89
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e89
            | exact resolve b7e89 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e89
          have b7e103 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
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
          have b7e128 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b7e103 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e103
          have b7e594 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e88 (σ x)
               have i₂ := b7e67
               grind)
            | exact superpose b7e67 b7e88
            | (have j0 := b7e88 (σ x)
               grind)
            | (have r₁ := b7e88 (σ x)
               have r₂ := b7e67
               grind)
            | exact resolve b7e88 b7e67
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e67 b7e88
          have b7e595 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by grind
          clear b7e594
          have b7e596 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have i₁ := b7e595
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e595
            | exact resolve b7e595 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e595
          have b7e597 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e596
               have r₂ := b7e94
               grind)
            | exact resolve b7e596 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e596
          have b7e598 : (M.op (σ x) (σ x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e597
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e597
            | exact resolve b7e597 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e597
          have b7e599 : (σ (M.op x x)) = (σ (k x y)) := by
            first
            | (have i₁ := b7e598
               have i₂ := b7e78 x
               grind)
            | exact superpose b7e78 b7e598
            | exact resolve b7e598 b7e78
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e78 b7e598
          have b7e601 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b7e599
               have i₂ := b7e128 x y
               grind)
            | exact superpose b7e128 b7e599
            | (have j1 := b7e128 x y
               grind)
            | exact resolve b7e599 b7e128
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e128
          have b7e603 : (k x y) = (τ (σ (M.op x x))) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e599
               grind)
            | exact superpose b7e599 b7e14
            | exact resolve b7e14 b7e599
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e599
          have b7e622 : (M.op x x) = (k x y) := by
            first
            | (have i₁ := b7e603
               have i₂ := b7e14 (M.op x x)
               grind)
            | exact superpose b7e14 b7e603
            | exact resolve b7e603 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e603
          have b7e624 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b7e601
               have r₂ := b7e94
               grind)
            | exact resolve b7e601 b7e94
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94 b7e601
          have b7e627 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b7e624
               have r₂ := b7e22
               grind)
            | exact resolve b7e624 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e624
          have b7e628 : (M.op x y) = (M.op x x) := by
            first
            | (have i₁ := b7e627
               have i₂ := b7e622
               grind)
            | exact superpose b7e622 b7e627
            | exact resolve b7e627 b7e622
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e622 b7e627
          have b7e629 : False := by grind
          exact b7e629
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
          have b8e113 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (M.op X0 (σ y)) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
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
          have b8e1003 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e113 (σ x)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e1004 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e1003
               have r₂ := b8e23
               grind)
            | exact resolve b8e1003 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1003
          have b8e1005 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e1004
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e1004
            | exact resolve b8e1004 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1004
          have b8e1010 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e1005
               grind)
            | exact superpose b8e1005 b8e20
            | exact resolve b8e20 b8e1005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1005
          have b8e1077 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
            first
            | (have i₁ := b8e1010
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e1010
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e1010 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1010
          have b8e1078 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
          clear b8e1077
          have b8e1080 : (M.op x y) = (M.op y y) := by
            first
            | (have r₁ := b8e1078
               have r₂ := b8e21
               grind)
            | exact resolve b8e1078 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e1078
          have b8e1083 : False := by grind
          exact b8e1083

/-- `Equation1286`: `x = y ◇ (((x ◇ y) ◇ x) ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then Y else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxy_y_y_x_pxy_Equation1286 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1286 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1286.models_iff G M).mp hM
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
        have b1e43 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
        have b1e45 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
        clear b1e43
        have b1e46 : (σ x) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e45
             have r₂ := b1e23
             grind)
          | exact resolve b1e45 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e45
        have b1e47 : (σ x) = (σ (k x y)) := by
          first
          | (have i₁ := b1e46
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e46
          | exact resolve b1e46 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e48 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e47
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e47
          | exact resolve b1e47 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e47
        have b1e49 : False := by grind
        exact b1e49
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
        have b2e51 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e51 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e51
        have b2e626 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e137 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e137
          | (have j0 := b2e137 x y
             grind)
          | exact resolve b2e137 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e137
        have b2e632 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
        clear b2e626
        have b2e638 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e632
             have r₂ := b2e22
             grind)
          | exact resolve b2e632 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e632
        have b2e644 : False := by grind
        exact b2e644
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
        have b3e42 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
        have b3e44 : x = y ∨ x = (k x y) := by grind
        clear b3e42
        have b3e45 : x = (k x y) := by
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
          have b5e41 : y ≠ y ∨ x = y ∨ x = (k x y) := by
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
          have b5e44 : x = y ∨ x = (k x y) := by grind
          clear b5e41
          have b5e46 : x = (k x y) := by
            first
            | (have r₁ := b5e44
               have r₂ := b5e25
               grind)
            | exact resolve b5e44 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e44
          have b5e49 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e163 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e49 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e49
          have b5e575 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e163 x y
               have i₂ := b5e46
               grind)
            | exact superpose b5e46 b5e163
            | (have j0 := b5e163 x y
               grind)
            | exact resolve b5e163 b5e46
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e46 b5e163
          have b5e578 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
          clear b5e575
          have b5e581 : (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e578
               have r₂ := b5e24
               grind)
            | exact resolve b5e578 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e578
          have b5e585 : False := by grind
          exact b5e585
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
        have b6e47 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
        have b6e49 : y = (M.op x y) ∨ x = (M.op x y) := by grind
        clear b6e47
        have b6e52 : x = (M.op x y) := by
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
          have b7e37 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by
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
          have b7e39 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e40 : (σ x) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e39
               have r₂ := b7e25
               grind)
            | exact resolve b7e39 b7e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e25 b7e39
          have b7e41 : (σ x) = (σ (k x y)) := by
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
          have b7e44 : (k x y) = (τ (σ x)) := by
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
          have b7e45 : x = (k x y) := by
            first
            | (have i₁ := b7e44
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e44
            | exact resolve b7e44 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e44
          have b7e55 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
          have b7e56 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b7e55
          have b7e58 : y = (M.op x y) := by
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
          have b8e113 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
          have b8e123 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e113
               have r₂ := b8e24
               grind)
            | exact resolve b8e113 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e113
          have b8e126 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e123
               have r₂ := b8e23
               grind)
            | exact resolve b8e123 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e123
          have b8e127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e126
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e126
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e126 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e126
          have b8e128 : y = (M.op x y) ∨ x = (M.op x y) := by grind
          clear b8e127
          have b8e129 : x = (M.op x y) := by
            first
            | (have r₁ := b8e128
               have r₂ := b8e22
               grind)
            | exact resolve b8e128 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e128
          have b8e130 : False := by grind
          exact b8e130
