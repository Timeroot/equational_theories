import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4277`: `x ◇ (x ◇ x) = y ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_y_pxy_Equation4277 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4277 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4277.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op y y) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op y y) := by grind
      have b0e20 : (σ y) = (M.op (σ y) (σ y)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e32 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y y) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 y y
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e11
        | exact resolve b0e11 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e33 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
        intro X0
        first
        | (have i₁ := b0e11 X0 (σ y) (σ y)
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e11
        | exact resolve b0e11 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e38 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
        intro X0
        first
        | (have i₁ := b0e33 X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e33
        | exact resolve b0e33 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e33
      have b0e39 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
        intro X0
        first
        | (have i₁ := b0e32 X0
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e32
        | exact resolve b0e32 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e32
      have b0e48 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 y) := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op X1 X1)
           have i₂ := b0e39 X1
           grind)
        | exact superpose b0e39 b0e11
        | exact resolve b0e11 b0e39
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e39
      have b0e49 : ∀ X1 : G, (σ y) = (M.op X1 y) := by
        intro X1
        first
        | (have i₁ := b0e48 x X1
           have i₂ := b0e38 x
           grind)
        | exact superpose b0e38 b0e48
        | exact resolve b0e48 b0e38
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e38 b0e48
      have b0e55 : y = (σ y) := by
        first
        | (have i₁ := b0e19
           have i₂ := b0e49 y
           grind)
        | exact superpose b0e49 b0e19
        | exact resolve b0e19 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e98 : (σ (M.op x y)) ≠ (M.op (σ x) y) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e18
        | exact resolve b0e18 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e103 : (σ (M.op x y)) ≠ (σ y) := by
        first
        | (have i₁ := b0e98
           have i₂ := b0e49 (σ x)
           grind)
        | exact superpose b0e49 b0e98
        | exact resolve b0e98 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e98
      have b0e104 : y ≠ (σ (M.op x y)) := by
        first
        | (have i₁ := b0e103
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e103
        | exact resolve b0e103 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e103
      have b0e105 : y ≠ (σ (σ y)) := by
        first
        | (have i₁ := b0e104
           have i₂ := b0e49 x
           grind)
        | exact superpose b0e49 b0e104
        | exact resolve b0e104 b0e49
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e49 b0e104
      have b0e106 : y ≠ (σ y) := by
        first
        | (have i₁ := b0e105
           have i₂ := b0e55
           grind)
        | exact superpose b0e55 b0e105
        | exact resolve b0e105 b0e55
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e105
      have b0e107 : False := by grind
      exact b0e107
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
      · have b1e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b1e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e20 : y = (M.op y y) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b1e46 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b1e15 X0 y
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e15
          | (have j0 := b1e15 X0 y
             grind)
          | (have r₁ := b1e15 X0 y
             have r₂ := b1e20
             grind)
          | exact resolve b1e15 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e48 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b1e46 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e46
        have b1e74 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e18 X0 X1
             have i₂ := b1e17 (σ X0) (σ X1)
             grind)
          | exact superpose b1e17 b1e18
          | (have j1 := b1e17 (σ X1) (σ X1)
             grind)
          | exact resolve b1e18 b1e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e77 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b1e74 X0 X1
             have i₂ := b1e48 (σ X1)
             grind)
          | exact superpose b1e48 b1e74
          | (have j0 := b1e74 X0 X1
             grind)
          | exact resolve b1e74 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b1e77 X0 X1
             have i₂ := b1e48 (σ X0)
             grind)
          | exact superpose b1e48 b1e77
          | (have j0 := b1e77 X0 X1
             grind)
          | exact resolve b1e77 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e77
        have b1e142 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e48 (σ y)
             grind)
          | exact superpose b1e48 b1e21
          | exact resolve b1e21 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e1543 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b1e21
             have i₂ := b1e83 y y
             grind)
          | exact superpose b1e83 b1e21
          | (have j1 := b1e83 y y
             grind)
          | exact resolve b1e21 b1e83
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e83
        have b1e1598 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b1e1543
        have b1e1628 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b1e1598
             have r₂ := b1e142
             grind)
          | exact resolve b1e1598 b1e142
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e142 b1e1598
        have b1e1639 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b1e1628
             have i₂ := b1e48 y
             grind)
          | exact superpose b1e48 b1e1628
          | exact resolve b1e1628 b1e48
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48 b1e1628
        have b1e1641 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b1e1639
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e1639
          | exact resolve b1e1639 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e1639
        have b1e1642 : False := by grind
        exact b1e1642
      · have b2e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e20 : y = (M.op y y) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e43 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have i₁ := b2e15 X0 y
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e15
          | (have j0 := b2e15 X0 y
             grind)
          | (have r₁ := b2e15 X0 y
             have r₂ := b2e20
             grind)
          | exact resolve b2e15 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
          intro X0
          first
          | (have j0 := b2e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e43
        have b2e68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e18 X0 X1
             have i₂ := b2e17 (σ X0) (σ X1)
             grind)
          | exact superpose b2e17 b2e18
          | (have j1 := b2e17 (σ X1) (σ X1)
             grind)
          | exact resolve b2e18 b2e17
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e71 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) y) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
          intro X0 X1
          first
          | (have i₁ := b2e68 X0 X1
             have i₂ := b2e44 (σ X1)
             grind)
          | exact superpose b2e44 b2e68
          | (have j0 := b2e68 X0 X1
             grind)
          | exact resolve b2e68 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e68
        have b2e77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (k (σ X1) y) ∨ (σ X1) = (k (σ X0) y) := by
          intro X0 X1
          first
          | (have i₁ := b2e71 X0 X1
             have i₂ := b2e44 (σ X0)
             grind)
          | exact superpose b2e44 b2e71
          | (have j0 := b2e71 X0 X1
             grind)
          | exact resolve b2e71 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e71
        have b2e130 : (σ y) ≠ (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e44 (σ y)
             grind)
          | exact superpose b2e44 b2e21
          | exact resolve b2e21 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e1093 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) ∨ (σ y) = (k (σ y) y) := by
          first
          | (have i₁ := b2e21
             have i₂ := b2e77 y y
             grind)
          | exact superpose b2e77 b2e21
          | (have j1 := b2e77 y y
             grind)
          | exact resolve b2e21 b2e77
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e77
        have b2e1140 : (σ y) ≠ (σ (k y y)) ∨ (σ y) = (k (σ y) y) := by grind
        clear b2e1093
        have b2e1166 : (σ y) ≠ (σ (k y y)) := by
          first
          | (have r₁ := b2e1140
             have r₂ := b2e130
             grind)
          | exact resolve b2e1140 b2e130
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e130 b2e1140
        have b2e1177 : (σ y) ≠ (σ (M.op y y)) := by
          first
          | (have i₁ := b2e1166
             have i₂ := b2e44 y
             grind)
          | exact superpose b2e44 b2e1166
          | exact resolve b2e1166 b2e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e44 b2e1166
        have b2e1180 : (σ y) ≠ (σ y) := by
          first
          | (have i₁ := b2e1177
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e1177
          | exact resolve b2e1177 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e1177
        have b2e1181 : False := by grind
        exact b2e1181
  · rcases eq_or_ne (M.op x x) (y) with h0b | h0b
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b3e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b3e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b3e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b3e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b3e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b3e20 : y ≠ (M.op y y) := by grind
        have b3e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b3e15 X0 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e15
          | (have j0 := b3e15 X0 (σ y)
             grind)
          | (have r₁ := b3e15 X0 (σ y)
             have r₂ := b3e22
             grind)
          | exact resolve b3e15 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b3e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e43
        have b3e116 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          grind
        have b3e122 : ∀ X0 X1 : G, (k X0 (σ y)) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b3e15 X1 X0
             have i₂ := b3e44 X0
             grind)
          | exact superpose b3e44 b3e15
          | (have j0 := b3e15 X1 X0
             grind)
          | exact resolve b3e15 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e44
        have b3e132 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b3e116 X0
             have j1 := b3e122 (M.op X0 X0) X0
             grind)
          | (have r₁ := b3e116 X0
             have r₂ := b3e122 (M.op X0 X0) x
             grind)
          | exact resolve b3e116 b3e122
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e116 b3e122
        have b3e225 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b3e132 (σ y)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e132
          | exact resolve b3e132 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e132
        have b3e229 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b3e225
             have i₂ := b3e18 y y
             grind)
          | exact superpose b3e18 b3e225
          | exact resolve b3e225 b3e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e225
        have b3e243 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b3e13 (k y y)
             have i₂ := b3e229
             grind)
          | exact superpose b3e229 b3e13
          | exact resolve b3e13 b3e229
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e229
        have b3e245 : y = (k y y) := by
          first
          | (have i₁ := b3e243
             have i₂ := b3e13 y
             grind)
          | exact superpose b3e13 b3e243
          | exact resolve b3e243 b3e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e243
        have b3e250 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b3e17 y y
             have i₂ := b3e245
             grind)
          | exact superpose b3e245 b3e17
          | (have j0 := b3e17 y y
             grind)
          | exact resolve b3e17 b3e245
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e245
        have b3e251 : y = (M.op y y) := by grind
        clear b3e250
        have b3e253 : False := by grind
        exact b3e253
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e32 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e42 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e32 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e32
            | exact resolve b4e32 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e44 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
            intro X0
            first
            | (have i₁ := b4e32 X0 (M.op X0 x)
               have i₂ := b4e32 X0 x
               grind)
            | exact superpose b4e32 b4e32
            | exact resolve b4e32 b4e32
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e78 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X2 X2) = (k X2 X1) ∨ (M.op X0 X0) = X0 ∨ (k X1 X0) = (M.op X1 X0) := by
            intro X0 X1 X2
            first
            | (have i₁ := b4e16 X2 X1
               have i₂ := b4e18 X1 X0
               grind)
            | (have i₁ := b4e16 X0 X1
               have i₂ := b4e18 X0 (M.op X1 X1)
               grind)
            | exact superpose b4e18 b4e16
            | (have j0 := b4e16 X2 X1
               have j1 := b4e18 X0 X0
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X0 X1
               grind)
            | (have r₁ := b4e16 X0 X1
               have r₂ := b4e18 X1 X1
               grind)
            | (have r₁ := b4e16 X0 (M.op X0 X0)
               have r₂ := b4e18 X0 (M.op (M.op X0 X0) (M.op X0 X0))
               grind)
            | exact resolve b4e16 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e92 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e20
            | exact resolve b4e20 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42
          have b4e1572 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e78 X1 X1 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e1573 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = (k X1 X1) := by
            intro X0 X1
            first
            | (have j0 := b4e1572 X0 X1
               have j1 := b4e16 X0 X1
               grind)
            | (have r₁ := b4e1572 X0 X1
               have r₂ := b4e16 X0 X1
               grind)
            | exact resolve b4e1572 b4e16
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1572
          have b4e1666 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1573 X0 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1573
          have b4e1667 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
            intro X0
            first
            | (have j0 := b4e1666 X0
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1666
          have b4e1814 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e19 X0 X0
               have i₂ := b4e1667 (σ X0)
               grind)
            | exact superpose b4e1667 b4e19
            | exact resolve b4e19 b4e1667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e1821 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            first
            | (have i₁ := b4e1814 X0
               have i₂ := b4e1667 X0
               grind)
            | exact superpose b4e1667 b4e1814
            | exact resolve b4e1814 b4e1667
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1667 b4e1814
          have b4e3118 : ∀ X0 : G, (M.op x y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e32 (σ X0) (σ X0)
               have i₂ := b4e1821 X0
               grind)
            | exact superpose b4e1821 b4e32
            | exact resolve b4e32 b4e1821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e32
          have b4e4623 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e3118 (M.op x y)
               have i₂ := b4e44 (M.op x y)
               grind)
            | exact superpose b4e44 b4e3118
            | exact resolve b4e3118 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e3118
          have b4e4686 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b4e4623
               have i₂ := b4e1821 (M.op x y)
               grind)
            | exact superpose b4e1821 b4e4623
            | exact resolve b4e4623 b4e1821
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1821 b4e4623
          have b4e4702 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e4686
               have i₂ := b4e44 (M.op x y)
               grind)
            | exact superpose b4e44 b4e4686
            | exact resolve b4e4686 b4e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e44 b4e4686
          have b4e4711 : False := by grind
          exact b4e4711
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op y y) := by grind
          have b5e22 : y = (M.op x x) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b5e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e32 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X0 X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e13 x X0 X1
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e13
            | exact resolve b5e13 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e35 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
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
          have b5e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b5e13 X2 X3 (M.op X3 X3)
               have i₂ := b5e13 X3 X0 X1
               grind)
            | (have i₁ := b5e13 X0 X1 (M.op X1 X2)
               have i₂ := b5e13 X0 X1 X2
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e76 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b5e24
               have i₂ := b5e18 (σ x) X0
               grind)
            | (have i₁ := b5e24
               have i₂ := b5e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b5e18 b5e24
            | (have j1 := b5e18 X0 X0
               grind)
            | (have r₁ := b5e24
               have r₂ := b5e18 (σ x) (σ y)
               grind)
            | exact resolve b5e24 b5e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e97 : y = (M.op y y) ∨ y = (k x y) := by grind
          have b5e115 : y = (k x y) := by
            first
            | (have r₁ := b5e97
               have r₂ := b5e21
               grind)
            | exact resolve b5e97 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e97
          have b5e812 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b5e76 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e76
          have b5e813 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b5e812
               have r₂ := b5e23
               grind)
            | exact resolve b5e812 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e812
          have b5e814 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b5e813
               have i₂ := b5e19 x y
               grind)
            | exact superpose b5e19 b5e813
            | exact resolve b5e813 b5e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e813
          have b5e815 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e814
               have i₂ := b5e115
               grind)
            | exact superpose b5e115 b5e814
            | exact resolve b5e814 b5e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e115 b5e814
          have b5e817 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (σ x) (σ y))) := by
            intro X0 X1
            first
            | (have i₁ := b5e36 (σ x) (σ y) X0 X1
               have i₂ := b5e815
               grind)
            | exact superpose b5e815 b5e36
            | exact resolve b5e36 b5e815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36
          have b5e820 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e32 (σ x) (σ y)
               have i₂ := b5e815
               grind)
            | exact superpose b5e815 b5e32
            | exact resolve b5e32 b5e815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e32
          have b5e823 : (M.op x y) = (σ y) := by
            first
            | (have i₁ := b5e820
               have i₂ := b5e815
               grind)
            | exact superpose b5e815 b5e820
            | exact resolve b5e820 b5e815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e820
          have b5e826 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (σ y)) := by
            intro X0 X1
            first
            | (have i₁ := b5e817 X0 X1
               have i₂ := b5e815
               grind)
            | exact superpose b5e815 b5e817
            | exact resolve b5e817 b5e815
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e815 b5e817
          have b5e830 : ∀ X1 : G, (M.op x y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b5e826 x X1
               have i₂ := b5e35 x
               grind)
            | exact superpose b5e35 b5e826
            | exact resolve b5e826 b5e35
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e826
          have b5e831 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
            intro X1
            first
            | (have i₁ := b5e830 X1
               have i₂ := b5e823
               grind)
            | exact superpose b5e823 b5e830
            | exact resolve b5e830 b5e823
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e823 b5e830
          have b5e1190 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e23
               have i₂ := b5e831 (σ y)
               grind)
            | exact superpose b5e831 b5e23
            | (have r₁ := b5e23
               have r₂ := b5e831 (σ y)
               grind)
            | exact resolve b5e23 b5e831
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e831
          have b5e1192 : False := by grind
          exact b5e1192
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ y)) with h1a | h1a
      · have b6e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
          intro X0 X1 X2
          grind
        have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
          intro X0 X1
          grind
        have b6e16 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op y y) := by grind
        have b6e22 : (σ y) = (M.op (σ y) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e29 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e12 X0 (σ y) (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e12
          | exact resolve b6e12 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e34 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ y) := by
          intro X0
          first
          | (have i₁ := b6e29 X0
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e29
          | exact resolve b6e29 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e29
        have b6e41 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (σ y)) := by
          intro X0 X1
          first
          | (have i₁ := b6e12 X0 X1 (M.op X1 X1)
             have i₂ := b6e34 X1
             grind)
          | exact superpose b6e34 b6e12
          | exact resolve b6e12 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e42 : ∀ X1 : G, (σ y) = (M.op X1 (σ y)) := by
          intro X1
          first
          | (have i₁ := b6e41 x X1
             have i₂ := b6e34 x
             grind)
          | exact superpose b6e34 b6e41
          | exact resolve b6e41 b6e34
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e34 b6e41
        have b6e43 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have i₁ := b6e15 X0 (σ y)
             have i₂ := b6e22
             grind)
          | exact superpose b6e22 b6e15
          | (have j0 := b6e15 X0 (σ y)
             grind)
          | (have r₁ := b6e15 X0 (σ y)
             have r₂ := b6e22
             grind)
          | exact resolve b6e15 b6e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b6e44 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) := by
          intro X0
          first
          | (have j0 := b6e43 X0
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e43
        have b6e115 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) (σ y)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          grind
        have b6e119 : ∀ X0 X1 : G, (k X0 (σ y)) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
          intro X0 X1
          first
          | (have i₁ := b6e15 X1 X0
             have i₂ := b6e44 X0
             grind)
          | exact superpose b6e44 b6e15
          | (have j0 := b6e15 X1 X0
             grind)
          | exact resolve b6e15 b6e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e44
        have b6e132 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
          intro X0
          first
          | (have j0 := b6e115 X0
             have j1 := b6e119 (M.op X0 X0) X0
             grind)
          | (have r₁ := b6e115 X0
             have r₂ := b6e119 (M.op X0 X0) x
             grind)
          | exact resolve b6e115 b6e119
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e115 b6e119
        have b6e149 : (σ y) = (k (σ y) (σ y)) := by
          first
          | (have i₁ := b6e132 (σ y)
             have i₂ := b6e42 (σ y)
             grind)
          | exact superpose b6e42 b6e132
          | exact resolve b6e132 b6e42
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e42 b6e132
        have b6e153 : (σ y) = (σ (k y y)) := by
          first
          | (have i₁ := b6e149
             have i₂ := b6e18 y y
             grind)
          | exact superpose b6e18 b6e149
          | exact resolve b6e149 b6e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e149
        have b6e167 : (k y y) = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 (k y y)
             have i₂ := b6e153
             grind)
          | exact superpose b6e153 b6e13
          | exact resolve b6e13 b6e153
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e153
        have b6e169 : y = (k y y) := by
          first
          | (have i₁ := b6e167
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e167
          | exact resolve b6e167 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e167
        have b6e258 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
          first
          | (have i₁ := b6e17 y y
             have i₂ := b6e169
             grind)
          | exact superpose b6e169 b6e17
          | (have j0 := b6e17 y y
             grind)
          | exact resolve b6e17 b6e169
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e169
        have b6e259 : y = (M.op y y) := by grind
        clear b6e258
        have b6e261 : False := by grind
        exact b6e261
      · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X1 X2)) := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op y y) := by grind
          have b7e22 : y ≠ (M.op x x) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b7e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e36 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 X2)) = (M.op X3 (M.op X0 (M.op X0 X1))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b7e13 X2 X3 (M.op X3 X3)
               have i₂ := b7e13 X3 X0 X1
               grind)
            | (have i₁ := b7e13 X0 X1 (M.op X1 X2)
               have i₂ := b7e13 X0 X1 X2
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e92 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          have b7e105 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e92
               have r₂ := b7e23
               grind)
            | exact resolve b7e92 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e92
          have b7e106 : (σ y) = (σ (k x y)) := by
            first
            | (have i₁ := b7e105
               have i₂ := b7e19 x y
               grind)
            | exact superpose b7e19 b7e105
            | exact resolve b7e105 b7e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e105
          have b7e112 : (k x y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (k x y)
               have i₂ := b7e106
               grind)
            | exact superpose b7e106 b7e14
            | exact resolve b7e14 b7e106
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e106
          have b7e113 : y = (k x y) := by
            first
            | (have i₁ := b7e112
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e112
            | exact resolve b7e112 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e112
          have b7e138 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b7e18 x y
               have i₂ := b7e113
               grind)
            | exact superpose b7e113 b7e18
            | (have j0 := b7e18 y y
               grind)
            | exact resolve b7e18 b7e113
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e113
          have b7e139 : y = (M.op x y) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b7e138
               have r₂ := b7e21
               grind)
            | exact resolve b7e138 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138
          have b7e141 : y = (M.op x y) := by
            first
            | (have r₁ := b7e139
               have r₂ := b7e22
               grind)
            | exact resolve b7e139 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e139
          have b7e186 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x y) := by
            intro X0
            first
            | (have i₁ := b7e13 X0 x y
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e13
            | exact resolve b7e13 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e187 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = y := by
            intro X0
            first
            | (have i₁ := b7e186 X0
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e186
            | exact resolve b7e186 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e186
          have b7e250 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b7e36 x y X0 X1
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e36
            | exact resolve b7e36 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e36
          have b7e298 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 y) := by
            intro X0 X1
            first
            | (have i₁ := b7e250 X0 X1
               have i₂ := b7e141
               grind)
            | exact superpose b7e141 b7e250
            | exact resolve b7e250 b7e141
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e141 b7e250
          have b7e320 : ∀ X1 : G, y = (M.op X1 y) := by
            intro X1
            first
            | (have i₁ := b7e298 x X1
               have i₂ := b7e187 x
               grind)
            | exact superpose b7e187 b7e298
            | exact resolve b7e298 b7e187
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e187 b7e298
          have b7e330 : y ≠ y := by
            first
            | (have i₁ := b7e21
               have i₂ := b7e320 y
               grind)
            | exact superpose b7e320 b7e21
            | (have r₁ := b7e21
               have r₂ := b7e320 y
               grind)
            | exact resolve b7e21 b7e320
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e320
          have b7e331 : False := by grind
          exact b7e331
        · have b8e18 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op y y) := by grind
          have b8e22 : y ≠ (M.op x x) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
          have b8e24 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e67 : ∀ X0 : G, (σ y) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
            intro X0
            first
            | (have i₁ := b8e24
               have i₂ := b8e18 (σ x) X0
               grind)
            | (have i₁ := b8e24
               have i₂ := b8e18 X0 (M.op (σ x) (σ x))
               grind)
            | exact superpose b8e18 b8e24
            | (have j1 := b8e18 X0 X0
               grind)
            | (have r₁ := b8e24
               have r₂ := b8e18 (σ x) (σ y)
               grind)
            | exact resolve b8e24 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e583 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have j0 := b8e67 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e67
          have b8e584 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e583
               have r₂ := b8e23
               grind)
            | exact resolve b8e583 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e583
          have b8e585 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e584
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e584
            | exact resolve b8e584 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e584
          have b8e586 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e585
               grind)
            | exact superpose b8e585 b8e20
            | exact resolve b8e20 b8e585
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e585
          have b8e671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e586
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e586
            | (have j1 := b8e18 y y
               grind)
            | exact resolve b8e586 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e586
          have b8e672 : y = (M.op y y) ∨ y = (M.op x x) := by grind
          clear b8e671
          have b8e674 : y = (M.op x x) := by
            first
            | (have r₁ := b8e672
               have r₂ := b8e21
               grind)
            | exact resolve b8e672 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e672
          have b8e676 : False := by grind
          exact b8e676

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_y_pxx_y_pxy_Equation4279 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4279 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
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
      have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e79 : False := by grind
      exact b0e79
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b4e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : y = (M.op x x) := by grind
          have b4e24 : (σ y) = (M.op (σ x) (σ x)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b4e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b4e30
          have b4e33 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b4e13 x X0 X1
               have i₂ := b4e22
               grind)
            | exact superpose b4e22 b4e13
            | exact resolve b4e13 b4e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e43 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e33 (σ x) (σ x)
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e33
            | exact resolve b4e33 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e45 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b4e33 (M.op X0 X1) X1
               have i₂ := b4e33 X1 X0
               grind)
            | exact superpose b4e33 b4e33
            | exact resolve b4e33 b4e33
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e95 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e43
               grind)
            | exact superpose b4e43 b4e20
            | exact resolve b4e20 b4e43
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e43
          have b4e121 : ∀ X0 : G, (M.op x y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b4e33 (σ X0) (σ X0)
               have i₂ := b4e31 X0
               grind)
            | exact superpose b4e31 b4e33
            | exact resolve b4e33 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e33
          have b4e922 : (M.op x y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            first
            | (have i₁ := b4e121 (M.op x y)
               have i₂ := b4e45 x y
               grind)
            | exact superpose b4e45 b4e121
            | exact resolve b4e121 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e121
          have b4e943 : (M.op x y) = (σ (M.op (M.op x y) (M.op x y))) := by
            first
            | (have i₁ := b4e922
               have i₂ := b4e31 (M.op x y)
               grind)
            | exact superpose b4e31 b4e922
            | exact resolve b4e922 b4e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e31 b4e922
          have b4e951 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b4e943
               have i₂ := b4e45 x y
               grind)
            | exact superpose b4e45 b4e943
            | exact resolve b4e943 b4e45
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e45 b4e943
          have b4e954 : False := by grind
          exact b4e954
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
          have b5e103 : (σ y) ≠ (σ (M.op x x)) := by
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
          have b5e113 : (σ y) ≠ (σ y) := by
            first
            | (have i₁ := b5e103
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e103
            | exact resolve b5e103 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e103
          have b5e114 : False := by grind
          exact b5e114
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
          have b7e100 : (σ y) = (σ (M.op x x)) := by
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
          have b7e138 : (M.op x x) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op x x)
               have i₂ := b7e100
               grind)
            | exact superpose b7e100 b7e14
            | exact resolve b7e14 b7e100
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e100
          have b7e139 : y = (M.op x x) := by
            first
            | (have i₁ := b7e138
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e138
            | exact resolve b7e138 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e138
          have b7e143 : False := by grind
          exact b7e143
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ X0 = X1 := by
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
          have b8e64 : ∀ X0 : G, (σ y) ≠ X0 ∨ (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ x) = X0 := by
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
          have b8e291 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
            first
            | (have j0 := b8e64 (σ y)
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e64
          have b8e292 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b8e291
               have r₂ := b8e23
               grind)
            | exact resolve b8e291 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e291
          have b8e293 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b8e292
               have i₂ := b8e19 x y
               grind)
            | exact superpose b8e19 b8e292
            | exact resolve b8e292 b8e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e292
          have b8e294 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e293
               grind)
            | exact superpose b8e293 b8e20
            | exact resolve b8e20 b8e293
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e293
          have b8e384 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e294
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e294
            | (have j1 := b8e18 x y
               grind)
            | (have r₁ := b8e294
               have r₂ := b8e18 (σ (M.op x y)) (σ (k x y))
               grind)
            | (have r₁ := b8e294
               have r₂ := b8e18 (σ (k x y)) (σ (M.op x y))
               grind)
            | exact resolve b8e294 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e294
          have b8e385 : y = (M.op x x) ∨ x = y := by grind
          clear b8e384
          have b8e387 : x = y := by
            first
            | (have r₁ := b8e385
               have r₂ := b8e22
               grind)
            | exact resolve b8e385 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e385
          have b8e389 : False := by grind
          exact b8e389

/-- `Equation4279`: `x ◇ (x ◇ x) = y ◇ (z ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pxy_pyx_Equation4279 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4279 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4279.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
      have b0e74 : (σ (M.op y y)) ≠ (σ (M.op y y)) := by grind
      clear b0e29
      have b0e79 : False := by grind
      exact b0e79
    · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
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
  · rcases eq_or_ne (M.op y y) (x) with h0b | h0b
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
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b4e17 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
            intro X0 X1
            grind
          have b4e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e21 : x ≠ y := by grind
          have b4e22 : x = (M.op y y) := by grind
          have b4e23 : (σ x) ≠ (σ y) := by grind
          have b4e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e77 : (M.op x y) = (k x y) ∨ x = y := by grind
          have b4e78 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
          have b4e81 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b4e78
               have r₂ := b4e23
               grind)
            | exact resolve b4e78 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e78
          have b4e82 : (M.op x y) = (k x y) := by
            first
            | (have r₁ := b4e77
               have r₂ := b4e21
               grind)
            | exact resolve b4e77 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e77
          have b4e83 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
            first
            | (have i₁ := b4e81
               have i₂ := b4e19 x y
               grind)
            | exact superpose b4e19 b4e81
            | exact resolve b4e81 b4e19
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e81
          have b4e84 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b4e83
               have i₂ := b4e82
               grind)
            | exact superpose b4e82 b4e83
            | exact resolve b4e83 b4e82
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e82 b4e83
          have b4e85 : False := by grind
          exact b4e85
        · have b5e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e22 : x = (M.op y y) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b5e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b5e30
          have b5e104 : (σ x) ≠ (σ (M.op y y)) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e31 y
               grind)
            | exact superpose b5e31 b5e24
            | exact resolve b5e24 b5e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e31
          have b5e114 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e104
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e104
            | exact resolve b5e104 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e104
          have b5e115 : False := by grind
          exact b5e115
    · rcases eq_or_ne ((σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e20 : x ≠ y := by grind
        have b6e22 : (σ x) = (σ y) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b6e26 : x = (τ (σ y)) := by
          first
          | (have i₁ := b6e13 x
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
             have i₂ := b6e13 y
             grind)
          | exact superpose b6e13 b6e26
          | exact resolve b6e26 b6e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e26
        have b6e28 : False := by grind
        exact b6e28
      · rcases eq_or_ne (M.op (σ y) (σ y)) ((σ x)) with h1b | h1b
        · have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e22 : x ≠ (M.op y y) := by grind
          have b7e24 : (σ x) = (M.op (σ y) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b7e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b7e30
          have b7e83 : (σ x) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e24
               have i₂ := b7e31 y
               grind)
            | exact superpose b7e31 b7e24
            | exact resolve b7e24 b7e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e31
          have b7e94 : (M.op y y) = (τ (σ x)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e83
               grind)
            | exact superpose b7e83 b7e14
            | exact resolve b7e14 b7e83
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e83
          have b7e95 : x = (M.op y y) := by
            first
            | (have i₁ := b7e94
               have i₂ := b7e14 x
               grind)
            | exact superpose b7e14 b7e94
            | exact resolve b7e94 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e94
          have b7e99 : False := by grind
          exact b7e99
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X2 X1)) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b8e16 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
            intro X0 X1
            grind
          have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : x ≠ y := by grind
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e31 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e30
          have b8e33 : ∀ X0 X1 X3 X4 : G, (M.op X0 (M.op X1 X0)) = (M.op X3 (M.op X4 X3)) := by
            intro X0 X1 X3 X4
            first
            | (have i₁ := b8e13 x X3 X4
               have i₂ := b8e13 x X0 X1
               grind)
            | (have i₁ := b8e13 x X1 x
               have i₂ := b8e13 X0 x x
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e36 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op X0 (M.op X0 X0))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e13 X1 (M.op X2 X3) X3
               have i₂ := b8e13 X0 X3 X2
               grind)
            | (have i₁ := b8e13 X0 (M.op X0 X0) X0
               have i₂ := b8e13 X0 X1 X2
               grind)
            | exact superpose b8e13 b8e13
            | exact resolve b8e13 b8e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e48 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
          have b8e54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e48 X0 X1
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e48
            | (have j0 := b8e48 X0 X1
               grind)
            | exact resolve b8e48 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e48
          have b8e80 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0 X1
            first
            | (have i₁ := b8e13 X1 (σ X0) (σ X0)
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e13
            | exact resolve b8e13 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e167 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (M.op (M.op X1 X2) (M.op X3 (M.op X3 X3))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e36 X3 (σ X0) X1 X2
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e36
            | exact resolve b8e36 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e186 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X2 X3) (M.op (σ X0) (σ (M.op X0 X0)))) := by
            intro X0 X1 X2 X3
            first
            | (have i₁ := b8e36 (σ X0) X1 X2 X3
               have i₂ := b8e31 X0
               grind)
            | exact superpose b8e31 b8e36
            | exact resolve b8e36 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e36
          have b8e607 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
          have b8e661 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e607
               have r₂ := b8e23
               grind)
            | exact resolve b8e607 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e607
          have b8e2656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e661
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e661
            | (have j1 := b8e18 y x
               grind)
            | (have r₁ := b8e661
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e661
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e661 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e661
          have b8e2664 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ x = y := by grind
          clear b8e2656
          have b8e2668 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
            first
            | (have r₁ := b8e2664
               have r₂ := b8e21
               grind)
            | exact resolve b8e2664 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2664
          have b8e2673 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e2668
               grind)
            | exact superpose b8e2668 b8e14
            | exact resolve b8e14 b8e2668
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2668
          have b8e2707 : y = (M.op x x) ∨ y = (M.op x x) := by
            first
            | (have i₁ := b8e2673
               have i₂ := b8e14 y
               grind)
            | exact superpose b8e14 b8e2673
            | exact resolve b8e2673 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2673
          have b8e2708 : y = (M.op x x) := by grind
          clear b8e2707
          have b8e2998 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ y)) := by
            intro X0
            first
            | (have i₁ := b8e80 x X0
               have i₂ := b8e2708
               grind)
            | exact superpose b8e2708 b8e80
            | exact resolve b8e80 b8e2708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3005 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op X1 X0)) := by
            intro X0 X1
            first
            | (have i₁ := b8e33 X0 X1 x x
               have i₂ := b8e2708
               grind)
            | exact superpose b8e2708 b8e33
            | exact resolve b8e33 b8e2708
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e33 b8e2708
          have b8e3019 : (M.op x y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e2998 x
               have i₂ := b8e3005 x x
               grind)
            | exact superpose b8e3005 b8e2998
            | exact resolve b8e2998 b8e3005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e2998
          have b8e3582 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op X0 X1) (M.op x y)) := by
            intro X0 X1
            first
            | (have i₁ := b8e3005 (M.op X0 X1) X1
               have i₂ := b8e3005 X1 X0
               grind)
            | exact superpose b8e3005 b8e3005
            | exact resolve b8e3005 b8e3005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e3686 : ∀ X0 : G, (M.op x y) = (M.op (σ X0) (σ (M.op X0 X0))) := by
            intro X0
            first
            | (have i₁ := b8e167 X0 x x x
               have i₂ := b8e3005 (M.op x x) x
               grind)
            | exact superpose b8e3005 b8e167
            | exact resolve b8e167 b8e3005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e167
          have b8e3950 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op (σ X2) (σ (M.op X2 X2)))) (σ (M.op X0 (M.op X0 X0)))) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e80 (M.op (σ X2) (σ (M.op X2 X2))) X1
               have i₂ := b8e186 X2 X0 (σ X2) (σ (M.op X2 X2))
               grind)
            | exact superpose b8e186 b8e80
            | exact resolve b8e80 b8e186
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e80 b8e186
          have b8e4001 : ∀ X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op (σ X2) (σ (M.op X2 X2)))) (σ (M.op x y))) := by
            intro X1 X2
            first
            | (have i₁ := b8e3950 x X1 X2
               have i₂ := b8e3005 x x
               grind)
            | exact superpose b8e3005 b8e3950
            | exact resolve b8e3950 b8e3005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3950
          have b8e4084 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
            intro X1
            first
            | (have i₁ := b8e4001 X1 x
               have i₂ := b8e3686 x
               grind)
            | exact superpose b8e3686 b8e4001
            | exact resolve b8e4001 b8e3686
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3686 b8e4001
          have b8e4111 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = (σ (M.op (M.op x y) (M.op x y))) := by
            intro X1
            first
            | (have i₁ := b8e4084 X1
               have i₂ := b8e31 (M.op x y)
               grind)
            | exact superpose b8e31 b8e4084
            | exact resolve b8e4084 b8e31
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e31 b8e4084
          have b8e4125 : ∀ X1 : G, (σ (M.op x y)) = (M.op X1 (M.op X1 X1)) := by
            intro X1
            first
            | (have i₁ := b8e4111 X1
               have i₂ := b8e3582 x y
               grind)
            | exact superpose b8e3582 b8e4111
            | exact resolve b8e4111 b8e3582
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3582 b8e4111
          have b8e4133 : (M.op x y) = (σ (M.op x y)) := by
            first
            | (have i₁ := b8e4125 x
               have i₂ := b8e3005 x x
               grind)
            | exact superpose b8e3005 b8e4125
            | exact resolve b8e4125 b8e3005
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3005 b8e4125
          have b8e4615 : (M.op x y) ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e3019
               grind)
            | exact superpose b8e3019 b8e20
            | exact resolve b8e20 b8e3019
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3019
          have b8e4661 : False := by grind
          exact b8e4661

/-- `Equation434`: `x = x ◇ (y ◇ (x ◇ (z ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_x_x_y_pxy_Equation434 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law434 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law434.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  rcases eq_or_ne (M.op x x) (y) with h0a | h0a
  · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
    · have b0e11 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
        intro X0 X1 X2
        grind
      have b0e18 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
      have b0e19 : y = (M.op x x) := by grind
      have b0e20 : (σ y) = (M.op (σ x) (σ x)) := by grind
      clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a
      have b0e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X0 X1 (M.op X0 (M.op x x))
           have i₂ := b0e11 X0 (M.op X0 (M.op x x)) x
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
        intro X0 X1
        first
        | (have i₁ := b0e11 X1 (M.op X0 X0) (M.op X0 X0)
           have i₂ := b0e11 (M.op X0 X0) X1 X0
           grind)
        | exact superpose b0e11 b0e11
        | exact resolve b0e11 b0e11
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      have b0e37 : x = (M.op x y) := by
        first
        | (have i₁ := b0e35 x x
           have i₂ := b0e19
           grind)
        | exact superpose b0e19 b0e35
        | exact resolve b0e35 b0e19
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e35
      have b0e77 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
        intro X0
        first
        | (have i₁ := b0e36 (σ x) X0
           have i₂ := b0e20
           grind)
        | exact superpose b0e20 b0e36
        | exact resolve b0e36 b0e20
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e36
      have b0e153 : (σ (M.op x y)) ≠ (σ x) := by
        first
        | (have i₁ := b0e18
           have i₂ := b0e77 (σ x)
           grind)
        | exact superpose b0e77 b0e18
        | exact resolve b0e18 b0e77
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e77
      have b0e155 : (σ x) ≠ (σ x) := by
        first
        | (have i₁ := b0e153
           have i₂ := b0e37
           grind)
        | exact superpose b0e37 b0e153
        | exact resolve b0e153 b0e37
        | grind
        | grind (splits := 40)
        | grind (splits := 40) (ematch := 20)
      clear b0e37 b0e153
      have b0e156 : False := by grind
      exact b0e156
    · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
      · have b1e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b1e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b1e16 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
          intro X0 X1
          grind
        have b1e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b1e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b1e20 : y = (M.op x x) := by grind
        have b1e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b1e22 : (σ x) = (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
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
        have b1e25 : x = (k x y) := by grind
        have b1e39 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
        have b1e44 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e39
        have b1e46 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e44
             have r₂ := b1e21
             grind)
          | exact resolve b1e44 b1e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e44
        have b1e48 : (σ y) = (σ (k x y)) := by
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
        have b1e49 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e48
             have i₂ := b1e25
             grind)
          | exact superpose b1e25 b1e48
          | exact resolve b1e48 b1e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e25 b1e48
        have b1e53 : y = (τ (σ x)) := by
          first
          | (have i₁ := b1e13 y
             have i₂ := b1e49
             grind)
          | exact superpose b1e49 b1e13
          | exact resolve b1e13 b1e49
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b1e54 : x = y := by
          first
          | (have i₁ := b1e53
             have i₂ := b1e13 x
             grind)
          | exact superpose b1e13 b1e53
          | exact resolve b1e53 b1e13
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e53
        have b1e74 : (σ x) ≠ (σ (M.op x x)) := by
          first
          | (have i₁ := b1e24
             have i₂ := b1e54
             grind)
          | exact superpose b1e54 b1e24
          | exact resolve b1e24 b1e54
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e24 b1e54
        have b1e76 : (σ x) ≠ (σ y) := by
          first
          | (have i₁ := b1e74
             have i₂ := b1e20
             grind)
          | exact superpose b1e20 b1e74
          | exact resolve b1e74 b1e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e74
        have b1e77 : False := by grind
        exact b1e77
      · have b2e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b2e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b2e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b2e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b2e20 : y = (M.op x x) := by grind
        have b2e21 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
        have b2e22 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h1a h1b
        have b2e24 : x = (k x y) := by grind
        have b2e28 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b2e12 X0 X1 (M.op X0 (M.op x x))
             have i₂ := b2e12 X0 (M.op X0 (M.op x x)) x
             grind)
          | exact superpose b2e12 b2e12
          | exact resolve b2e12 b2e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b2e30 : x = (M.op x y) := by
          first
          | (have i₁ := b2e28 x x
             have i₂ := b2e20
             grind)
          | exact superpose b2e20 b2e28
          | exact resolve b2e28 b2e20
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e28
        have b2e50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
        have b2e175 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
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
        clear b2e50
        have b2e212 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e175
             have r₂ := b2e21
             grind)
          | exact resolve b2e175 b2e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e175
        have b2e217 : (σ (M.op x y)) ≠ (σ (k x y)) := by
          first
          | (have r₁ := b2e212
             have r₂ := b2e22
             grind)
          | exact resolve b2e212 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e212
        have b2e218 : (σ (M.op x y)) ≠ (σ x) := by
          first
          | (have i₁ := b2e217
             have i₂ := b2e24
             grind)
          | exact superpose b2e24 b2e217
          | exact resolve b2e217 b2e24
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e24 b2e217
        have b2e219 : (σ x) ≠ (σ x) := by
          first
          | (have i₁ := b2e218
             have i₂ := b2e30
             grind)
          | exact superpose b2e30 b2e218
          | exact resolve b2e218 b2e30
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e30 b2e218
        have b2e220 : False := by grind
        exact b2e220
  · rcases eq_or_ne (M.op x y) (x) with h0b | h0b
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b3e12 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
          intro X0 X1 X2
          grind
        have b3e19 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
        have b3e21 : x = (M.op x y) := by grind
        have b3e22 : (σ y) = (M.op (σ x) (σ x)) := by grind
        clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a
        have b3e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e19
             have i₂ := b3e21
             grind)
          | exact superpose b3e21 b3e19
          | exact resolve b3e19 b3e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e42 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
          intro X0 X1
          first
          | (have i₁ := b3e12 X0 X1 (M.op X0 (M.op x x))
             have i₂ := b3e12 X0 (M.op X0 (M.op x x)) x
             grind)
          | exact superpose b3e12 b3e12
          | exact resolve b3e12 b3e12
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        have b3e45 : (σ x) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b3e42 (σ x) (σ x)
             have i₂ := b3e22
             grind)
          | exact superpose b3e22 b3e42
          | exact resolve b3e42 b3e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e42
        have b3e51 : False := by grind
        exact b3e51
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b4e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b4e22 : x = (M.op x y) := by grind
          have b4e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b4e26 : (σ (M.op x y)) ≠ (σ x) := by
            first
            | (have i₁ := b4e20
               have i₂ := b4e24
               grind)
            | exact superpose b4e24 b4e20
            | exact resolve b4e20 b4e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b4e27 : (σ x) ≠ (σ x) := by
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
        · have b5e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b5e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b5e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b5e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b5e21 : y ≠ (M.op x x) := by grind
          have b5e22 : x = (M.op x y) := by grind
          have b5e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b5e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b5e35 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X0 X1 (M.op X0 (M.op x x))
               have i₂ := b5e13 X0 (M.op X0 (M.op x x)) x
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e36 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b5e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b5e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b5e13 b5e13
            | exact resolve b5e13 b5e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b5e43 : x ≠ x ∨ y = (M.op x x) ∨ y = (k x y) := by
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
          have b5e48 : y = (M.op x x) ∨ y = (k x y) := by grind
          clear b5e43
          have b5e50 : y = (k x y) := by
            first
            | (have r₁ := b5e48
               have r₂ := b5e21
               grind)
            | exact resolve b5e48 b5e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48
          have b5e55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b5e156 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have i₁ := b5e35 (σ X1) (σ X0)
               have i₂ := b5e55 X0 X1
               grind)
            | exact superpose b5e55 b5e35
            | (have j1 := b5e55 X0 X1
               grind)
            | exact resolve b5e35 b5e55
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e35 b5e55
          have b5e1509 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e156 x y
               have i₂ := b5e50
               grind)
            | exact superpose b5e50 b5e156
            | (have j0 := b5e156 y y
               grind)
            | exact resolve b5e156 b5e50
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e50 b5e156
          have b5e1632 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e1509
               have r₂ := b5e23
               grind)
            | exact resolve b5e1509 b5e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1509
          have b5e1639 : (σ y) = (M.op (σ y) (σ y)) := by
            first
            | (have r₁ := b5e1632
               have r₂ := b5e24
               grind)
            | exact resolve b5e1632 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1632
          have b5e1657 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
            intro X0
            first
            | (have i₁ := b5e36 (σ y) X0
               have i₂ := b5e1639
               grind)
            | exact superpose b5e1639 b5e36
            | exact resolve b5e36 b5e1639
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e36 b5e1639
          have b5e2846 : (σ x) ≠ (σ x) := by
            first
            | (have i₁ := b5e24
               have i₂ := b5e1657 (σ x)
               grind)
            | exact superpose b5e1657 b5e24
            | (have r₁ := b5e24
               have r₂ := b5e1657 (σ x)
               grind)
            | exact resolve b5e24 b5e1657
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e1657
          have b5e2847 : False := by grind
          exact b5e2847
    · rcases eq_or_ne (M.op (σ x) (σ x)) ((σ y)) with h1a | h1a
      · have b6e13 : ∀ X0 : G, (τ (σ X0)) = X0 := by
          intro X0
          grind
        have b6e15 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e17 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
          intro X0 X1
          grind
        have b6e18 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
          intro X0 X1
          grind
        have b6e20 : y ≠ (M.op x x) := by grind
        have b6e21 : x ≠ (M.op x y) := by grind
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
        have b6e72 : x = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
        have b6e84 : x = (M.op x y) ∨ y = (M.op x x) := by grind
        clear b6e72
        have b6e87 : y = (M.op x x) := by
          first
          | (have r₁ := b6e84
             have r₂ := b6e21
             grind)
          | exact resolve b6e84 b6e21
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b6e84
        have b6e90 : False := by grind
        exact b6e90
      · rcases eq_or_ne (M.op (σ x) (σ y)) ((σ x)) with h1b | h1b
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 (M.op X2 X2)))) = X0 := by
            intro X0 X1 X2
            grind
          have b7e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
            intro X0
            grind
          have b7e17 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X1 := by
            intro X0 X1
            grind
          have b7e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b7e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b7e21 : y ≠ (M.op x x) := by grind
          have b7e22 : x ≠ (M.op x y) := by grind
          have b7e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b7e24 : (σ x) = (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b7e29 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X0 X1 (M.op X0 (M.op x x))
               have i₂ := b7e13 X0 (M.op X0 (M.op x x)) x
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e30 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
            intro X0 X1
            first
            | (have i₁ := b7e13 X1 (M.op X0 X0) (M.op X0 X0)
               have i₂ := b7e13 (M.op X0 X0) X1 X0
               grind)
            | exact superpose b7e13 b7e13
            | exact resolve b7e13 b7e13
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e37 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by
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
          have b7e42 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e37
          have b7e44 : (σ y) = (k (σ x) (σ y)) := by
            first
            | (have r₁ := b7e42
               have r₂ := b7e23
               grind)
            | exact resolve b7e42 b7e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e42
          have b7e46 : (σ y) = (σ (k x y)) := by
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
          have b7e72 : (k x y) = (τ (σ y)) := by
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
          have b7e73 : y = (k x y) := by
            first
            | (have i₁ := b7e72
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e72
            | exact resolve b7e72 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e72
          have b7e86 : y = (M.op x y) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
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
          have b7e87 : y = (M.op x y) ∨ x = (M.op x y) := by
            first
            | (have r₁ := b7e86
               have r₂ := b7e21
               grind)
            | exact resolve b7e86 b7e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e86
          have b7e89 : y = (M.op x y) := by
            first
            | (have r₁ := b7e87
               have r₂ := b7e22
               grind)
            | exact resolve b7e87 b7e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e87
          have b7e103 : y = (M.op y y) := by
            first
            | (have i₁ := b7e29 y x
               have i₂ := b7e89
               grind)
            | exact superpose b7e89 b7e29
            | exact resolve b7e29 b7e89
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e29 b7e89
          have b7e185 : ∀ X0 : G, (M.op X0 y) = X0 := by
            intro X0
            first
            | (have i₁ := b7e30 y X0
               have i₂ := b7e103
               grind)
            | exact superpose b7e103 b7e30
            | exact resolve b7e30 b7e103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e103
          have b7e202 : x ≠ x := by
            first
            | (have i₁ := b7e22
               have i₂ := b7e185 x
               grind)
            | exact superpose b7e185 b7e22
            | (have r₁ := b7e22
               have r₂ := b7e185 x
               grind)
            | exact resolve b7e22 b7e185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e185
          have b7e203 : False := by grind
          exact b7e203
        · have b8e18 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X0 := by
            intro X0 X1
            grind
          have b8e19 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
            intro X0 X1
            grind
          have b8e20 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
          have b8e21 : y ≠ (M.op x x) := by grind
          have b8e22 : x ≠ (M.op x y) := by grind
          have b8e23 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
          have b8e24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
          have b8e153 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e52 x y
               grind)
            | exact superpose b8e52 b8e20
            | (have j1 := b8e52 x y
               grind)
            | exact resolve b8e20 b8e52
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e52
          have b8e195 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e153
               have r₂ := b8e23
               grind)
            | exact resolve b8e153 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e153
          have b8e200 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e195
               have r₂ := b8e24
               grind)
            | exact resolve b8e195 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e195
          have b8e201 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
            first
            | (have i₁ := b8e200
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e200
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e200 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e200
          have b8e202 : y = (M.op x x) ∨ x = (M.op x y) := by grind
          clear b8e201
          have b8e203 : x = (M.op x y) := by
            first
            | (have r₁ := b8e202
               have r₂ := b8e21
               grind)
            | exact resolve b8e202 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e202
          have b8e204 : False := by grind
          exact b8e204

/-- `Equation4343`: `x ◇ (y ◇ y) = y ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(X,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_x_x_y_pxy_Equation4343 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4343 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4343.models_iff G M).mp hM
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
        have b1e48 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
        clear b1e45
        have b1e49 : (σ y) = (k (σ x) (σ y)) := by
          first
          | (have r₁ := b1e48
             have r₂ := b1e23
             grind)
          | exact resolve b1e48 b1e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e48
        have b1e50 : (σ y) = (σ (k x y)) := by
          first
          | (have i₁ := b1e49
             have i₂ := b1e18 x y
             grind)
          | exact superpose b1e18 b1e49
          | exact resolve b1e49 b1e18
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e49
        have b1e51 : (σ x) = (σ y) := by
          first
          | (have i₁ := b1e50
             have i₂ := b1e28
             grind)
          | exact superpose b1e28 b1e50
          | exact resolve b1e50 b1e28
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b1e28 b1e50
        have b1e52 : False := by grind
        exact b1e52
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
        have b2e56 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
        have b2e115 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
          intro X0 X1
          first
          | (have j0 := b2e56 X0 X1
             grind)
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e56
        have b2e478 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have i₁ := b2e115 x y
             have i₂ := b2e25
             grind)
          | exact superpose b2e25 b2e115
          | (have j0 := b2e115 x y
             grind)
          | exact resolve b2e115 b2e25
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e25 b2e115
        have b2e481 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
        clear b2e478
        have b2e485 : (σ y) = (M.op (σ x) (σ y)) := by
          first
          | (have r₁ := b2e481
             have r₂ := b2e22
             grind)
          | exact resolve b2e481 b2e22
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b2e481
        have b2e489 : False := by grind
        exact b2e489
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
        have b3e43 : x = y ∨ y = (k x y) := by grind
        clear b3e40
        have b3e44 : y = (k x y) := by
          first
          | (have r₁ := b3e43
             have r₂ := b3e23
             grind)
          | exact resolve b3e43 b3e23
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e23 b3e43
        have b3e47 : (σ x) = (σ y) := by
          first
          | (have i₁ := b3e29
             have i₂ := b3e44
             grind)
          | exact superpose b3e44 b3e29
          | exact resolve b3e29 b3e44
          | grind
          | grind (splits := 40)
          | grind (splits := 40) (ematch := 20)
        clear b3e29 b3e44
        have b3e48 : False := by grind
        exact b3e48
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
          have b5e47 : x = y ∨ y = (k x y) := by grind
          clear b5e44
          have b5e48 : y = (k x y) := by
            first
            | (have r₁ := b5e47
               have r₂ := b5e25
               grind)
            | exact resolve b5e47 b5e25
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e25 b5e47
          have b5e52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b5e112 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
            intro X0 X1
            first
            | (have j0 := b5e52 X0 X1
               grind)
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e52
          have b5e460 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b5e112 x y
               have i₂ := b5e48
               grind)
            | exact superpose b5e48 b5e112
            | (have j0 := b5e112 x y
               grind)
            | exact resolve b5e112 b5e48
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e48 b5e112
          have b5e463 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
          clear b5e460
          have b5e466 : (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b5e463
               have r₂ := b5e24
               grind)
            | exact resolve b5e463 b5e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e463
          have b5e470 : False := by grind
          exact b5e470
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
          have b7e39 : (σ x) = (σ y) ∨ (σ y) = (k (σ x) (σ y)) := by grind
          clear b7e36
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
          have b8e44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
          have b8e92 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e44 x y
               grind)
            | exact superpose b8e44 b8e20
            | (have j1 := b8e44 x y
               grind)
            | exact resolve b8e20 b8e44
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e44
          have b8e109 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
            first
            | (have r₁ := b8e92
               have r₂ := b8e24
               grind)
            | exact resolve b8e92 b8e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e92
          have b8e112 : (σ (M.op x y)) ≠ (σ (k x y)) := by
            first
            | (have r₁ := b8e109
               have r₂ := b8e23
               grind)
            | exact resolve b8e109 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e109
          have b8e113 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
            first
            | (have i₁ := b8e112
               have i₂ := b8e18 x y
               grind)
            | exact superpose b8e18 b8e112
            | (have j1 := b8e18 x y
               grind)
            | exact resolve b8e112 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e112
          have b8e114 : x = (M.op x y) ∨ y = (M.op x y) := by grind
          clear b8e113
          have b8e115 : y = (M.op x y) := by
            first
            | (have r₁ := b8e114
               have r₂ := b8e22
               grind)
            | exact resolve b8e114 b8e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e114
          have b8e116 : False := by grind
          exact b8e116

/-- `Equation4393`: `x ◇ (x ◇ x) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pyx_Equation4393 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4393 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4393.models_iff G M).mp hM
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
        · have b4e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
          have b4e32 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X1) X1) := by
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
          have b4e41 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X1) := by
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
          have b4e983 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
          have b4e1017 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b4e983
               have r₂ := b4e23
               grind)
            | exact resolve b4e983 b4e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e983
          have b4e1671 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b4e1017
               have i₂ := b4e18 y x
               grind)
            | exact superpose b4e18 b4e1017
            | (have j1 := b4e18 (M.op x x) x
               grind)
            | (have r₁ := b4e1017
               have r₂ := b4e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b4e1017
               have r₂ := b4e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b4e1017 b4e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1017
          have b4e1672 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b4e1671
          have b4e1676 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b4e1672
               have r₂ := b4e21
               grind)
            | exact resolve b4e1672 b4e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1672
          have b4e5137 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e14 (M.op x x)
               have i₂ := b4e1676
               grind)
            | exact superpose b4e1676 b4e14
            | exact resolve b4e14 b4e1676
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e1676
          have b4e5184 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b4e5137
               have i₂ := b4e14 x
               grind)
            | exact superpose b4e14 b4e5137
            | exact resolve b4e5137 b4e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5137
          have b4e5185 : x = (M.op x x) := by grind
          clear b4e5184
          have b4e5395 : (σ y) = (M.op x x) := by
            first
            | (have i₁ := b4e41 x x
               have i₂ := b4e5185
               grind)
            | exact superpose b4e5185 b4e41
            | exact resolve b4e41 b4e5185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e41
          have b4e5399 : x = (σ y) := by
            first
            | (have i₁ := b4e5395
               have i₂ := b4e5185
               grind)
            | exact superpose b4e5185 b4e5395
            | exact resolve b4e5395 b4e5185
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e5185 b4e5395
          have b4e5416 : x = y := by
            first
            | (have i₁ := b4e5399
               have i₂ := b4e42
               grind)
            | exact superpose b4e42 b4e5399
            | exact resolve b4e5399 b4e42
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b4e42 b4e5399
          have b4e5433 : False := by grind
          exact b4e5433
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
          have b5e112 : (σ y) ≠ (σ (M.op y y)) := by
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
            | (have i₁ := b5e112
               have i₂ := b5e22
               grind)
            | exact superpose b5e22 b5e112
            | exact resolve b5e112 b5e22
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b5e112
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
        · have b7e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
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
          have b7e32 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 X1) X1) := by
            intro X0 X1
            first
            | (have i₁ := b7e13 (σ y) X0 X1
               have i₂ := b7e24
               grind)
            | exact superpose b7e24 b7e13
            | exact resolve b7e13 b7e24
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b7e39 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 X1) X1) := by
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
          have b7e50 : ∀ X1 : G, (σ y) = (M.op (σ y) X1) := by
            intro X1
            first
            | (have i₁ := b7e39 (M.op x X1) X1
               have i₂ := b7e39 x X1
               grind)
            | exact superpose b7e39 b7e39
            | exact resolve b7e39 b7e39
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e39
          have b7e115 : (σ y) = (σ (M.op y y)) := by
            first
            | (have i₁ := b7e50 (σ y)
               have i₂ := b7e30 y
               grind)
            | exact superpose b7e30 b7e50
            | exact resolve b7e50 b7e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e30 b7e50
          have b7e136 : (M.op y y) = (τ (σ y)) := by
            first
            | (have i₁ := b7e14 (M.op y y)
               have i₂ := b7e115
               grind)
            | exact superpose b7e115 b7e14
            | exact resolve b7e14 b7e115
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e115
          have b7e137 : y = (M.op y y) := by
            first
            | (have i₁ := b7e136
               have i₂ := b7e14 y
               grind)
            | exact superpose b7e14 b7e136
            | exact resolve b7e136 b7e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b7e136
          have b7e141 : False := by grind
          exact b7e141
        · have b8e13 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 X2) X2) := by
            intro X0 X1 X2
            grind
          have b8e14 : ∀ X0 : G, (τ (σ X0)) = X0 := by
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
          have b8e23 : (σ x) ≠ (σ y) := by grind
          clear hm ht hu hv hd nh hM hi1 hi2 h0a h0b h1a h1b
          have b8e29 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
            intro X0
            grind
          have b8e30 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
            intro X0
            grind
          clear b8e29
          have b8e34 : ∀ X0 X1 X3 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op X0 (M.op X0 X0)) X3) := by
            intro X0 X1 X3
            first
            | (have i₁ := b8e13 X1 (M.op x X3) X3
               have i₂ := b8e13 X0 x X3
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
          clear b8e35
          have b8e139 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X1)) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X2) := by
            intro X0 X1 X2
            first
            | (have i₁ := b8e34 (σ X0) X1 X2
               have i₂ := b8e30 X0
               grind)
            | exact superpose b8e30 b8e34
            | exact resolve b8e34 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e34
          have b8e629 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
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
          have b8e658 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
            first
            | (have r₁ := b8e629
               have r₂ := b8e23
               grind)
            | exact resolve b8e629 b8e23
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e629
          have b8e3914 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by
            first
            | (have i₁ := b8e658
               have i₂ := b8e18 y x
               grind)
            | exact superpose b8e18 b8e658
            | (have j1 := b8e18 (M.op x x) x
               grind)
            | (have r₁ := b8e658
               have r₂ := b8e18 (σ (M.op x y)) (σ (k y x))
               grind)
            | (have r₁ := b8e658
               have r₂ := b8e18 (σ (k y x)) (σ (M.op x y))
               grind)
            | exact resolve b8e658 b8e18
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e658
          have b8e3915 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = y := by grind
          clear b8e3914
          have b8e3917 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
            first
            | (have r₁ := b8e3915
               have r₂ := b8e21
               grind)
            | exact resolve b8e3915 b8e21
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3915
          have b8e3925 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e14 (M.op x x)
               have i₂ := b8e3917
               grind)
            | exact superpose b8e3917 b8e14
            | exact resolve b8e14 b8e3917
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3917
          have b8e3963 : x = (M.op x x) ∨ x = (M.op x x) := by
            first
            | (have i₁ := b8e3925
               have i₂ := b8e14 x
               grind)
            | exact superpose b8e14 b8e3925
            | exact resolve b8e3925 b8e14
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3925
          have b8e3964 : x = (M.op x x) := by grind
          clear b8e3963
          have b8e4036 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) (σ x)) := by
            intro X0
            first
            | (have i₁ := b8e103 x X0
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e103
            | exact resolve b8e103 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e103
          have b8e4040 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e139 x X0 X1
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e139
            | exact resolve b8e139 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e139
          have b8e4048 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x x) := by
            intro X0
            first
            | (have i₁ := b8e13 X0 x x
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e13
            | exact resolve b8e13 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e4065 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = x := by
            intro X0
            first
            | (have i₁ := b8e4048 X0
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e4048
            | exact resolve b8e4048 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4048
          have b8e4073 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ (M.op x x)) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e4040 X0 X1
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e4040
            | exact resolve b8e4040 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4040
          have b8e4077 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ (M.op x x)) := by
            intro X0
            first
            | (have i₁ := b8e4036 X0
               have i₂ := b8e30 x
               grind)
            | exact superpose b8e30 b8e4036
            | exact resolve b8e4036 b8e30
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e30 b8e4036
          have b8e4092 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ x) X1) := by
            intro X0 X1
            first
            | (have i₁ := b8e4073 X0 X1
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e4073
            | exact resolve b8e4073 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4073
          have b8e4095 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (σ x) := by
            intro X0
            first
            | (have i₁ := b8e4077 X0
               have i₂ := b8e3964
               grind)
            | exact superpose b8e3964 b8e4077
            | exact resolve b8e4077 b8e3964
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e3964 b8e4077
          have b8e4103 : ∀ X1 : G, x = (M.op (σ x) X1) := by
            intro X1
            first
            | (have i₁ := b8e4092 x X1
               have i₂ := b8e4065 x
               grind)
            | exact superpose b8e4065 b8e4092
            | exact resolve b8e4092 b8e4065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4092
          have b8e4104 : x = (σ x) := by
            first
            | (have i₁ := b8e4095 x
               have i₂ := b8e4065 x
               grind)
            | exact superpose b8e4065 b8e4095
            | exact resolve b8e4095 b8e4065
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4065 b8e4095
          have b8e5993 : ∀ X0 : G, x = (M.op x X0) := by
            intro X0
            first
            | (have i₁ := b8e4103 X0
               have i₂ := b8e4104
               grind)
            | exact superpose b8e4104 b8e4103
            | exact resolve b8e4103 b8e4104
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          have b8e6016 : x ≠ (σ (M.op x y)) := by
            first
            | (have i₁ := b8e20
               have i₂ := b8e4103 (σ y)
               grind)
            | exact superpose b8e4103 b8e20
            | exact resolve b8e20 b8e4103
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e4103
          have b8e7516 : x ≠ (σ x) := by
            first
            | (have i₁ := b8e6016
               have i₂ := b8e5993 y
               grind)
            | exact superpose b8e5993 b8e6016
            | exact resolve b8e6016 b8e5993
            | grind
            | grind (splits := 40)
            | grind (splits := 40) (ematch := 20)
          clear b8e5993 b8e6016
          have b8e7517 : False := by grind
          exact b8e7517
